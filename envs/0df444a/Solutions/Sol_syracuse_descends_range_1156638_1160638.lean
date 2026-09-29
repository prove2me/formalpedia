-- Prove2me | solution 1 for syracuse_descends_range_1156638_1160638
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:49.178943+00:00
-- url     : https://prove2.me/submissions/9056ea87-9663-40f8-b802-4c18a15b955d

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


theorem B1736717 : Blo 1156638 1736717 := bbase (se 3 (by rfl) ⟨325634, by rfl⟩ : syracuseStep 1736717 = 651269) (by norm_num)
theorem B1736741 : Blo 1156638 1736741 := bbase (se 4 (by rfl) ⟨162819, by rfl⟩ : syracuseStep 1736741 = 325639) (by norm_num)
theorem B1736765 : Blo 1156638 1736765 := bbase (se 3 (by rfl) ⟨325643, by rfl⟩ : syracuseStep 1736765 = 651287) (by norm_num)
theorem B1736789 : Blo 1156638 1736789 := bbase (se 8 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 1736789 = 20353) (by norm_num)
theorem B1736813 : Blo 1156638 1736813 := bbase (se 3 (by rfl) ⟨325652, by rfl⟩ : syracuseStep 1736813 = 651305) (by norm_num)
theorem B1736837 : Blo 1156638 1736837 := bbase (se 4 (by rfl) ⟨162828, by rfl⟩ : syracuseStep 1736837 = 325657) (by norm_num)
theorem B1736861 : Blo 1156638 1736861 := bbase (se 3 (by rfl) ⟨325661, by rfl⟩ : syracuseStep 1736861 = 651323) (by norm_num)
theorem B1736885 : Blo 1156638 1736885 := bbase (se 5 (by rfl) ⟨81416, by rfl⟩ : syracuseStep 1736885 = 162833) (by norm_num)
theorem B1736909 : Blo 1156638 1736909 := bbase (se 3 (by rfl) ⟨325670, by rfl⟩ : syracuseStep 1736909 = 651341) (by norm_num)
theorem B1736933 : Blo 1156638 1736933 := bbase (se 4 (by rfl) ⟨162837, by rfl⟩ : syracuseStep 1736933 = 325675) (by norm_num)
theorem B1736957 : Blo 1156638 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1736981 : Blo 1156638 1736981 := bbase (se 6 (by rfl) ⟨40710, by rfl⟩ : syracuseStep 1736981 = 81421) (by norm_num)
theorem B1737005 : Blo 1156638 1737005 := bbase (se 3 (by rfl) ⟨325688, by rfl⟩ : syracuseStep 1737005 = 651377) (by norm_num)
theorem B1737029 : Blo 1156638 1737029 := bbase (se 4 (by rfl) ⟨162846, by rfl⟩ : syracuseStep 1737029 = 325693) (by norm_num)
theorem B1737053 : Blo 1156638 1737053 := bbase (se 3 (by rfl) ⟨325697, by rfl⟩ : syracuseStep 1737053 = 651395) (by norm_num)
theorem B1737077 : Blo 1156638 1737077 := bbase (se 5 (by rfl) ⟨81425, by rfl⟩ : syracuseStep 1737077 = 162851) (by norm_num)
theorem B1737101 : Blo 1156638 1737101 := bbase (se 3 (by rfl) ⟨325706, by rfl⟩ : syracuseStep 1737101 = 651413) (by norm_num)
theorem B1737125 : Blo 1156638 1737125 := bbase (se 4 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 1737125 = 325711) (by norm_num)
theorem B2195885 : Blo 1156638 2195885 := bbase (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) (by norm_num)
theorem B6685109 : Blo 1156638 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B1737149 : Blo 1156638 1737149 := bbase (se 3 (by rfl) ⟨325715, by rfl⟩ : syracuseStep 1737149 = 651431) (by norm_num)
theorem B1737173 : Blo 1156638 1737173 := bbase (se 7 (by rfl) ⟨20357, by rfl⟩ : syracuseStep 1737173 = 40715) (by norm_num)
theorem B1737197 : Blo 1156638 1737197 := bbase (se 3 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 1737197 = 651449) (by norm_num)
theorem B1737221 : Blo 1156638 1737221 := bbase (se 4 (by rfl) ⟨162864, by rfl⟩ : syracuseStep 1737221 = 325729) (by norm_num)
theorem B1737245 : Blo 1156638 1737245 := bbase (se 3 (by rfl) ⟨325733, by rfl⟩ : syracuseStep 1737245 = 651467) (by norm_num)
theorem B1737269 : Blo 1156638 1737269 := bbase (se 5 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 1737269 = 162869) (by norm_num)
theorem B1737293 : Blo 1156638 1737293 := bbase (se 3 (by rfl) ⟨325742, by rfl⟩ : syracuseStep 1737293 = 651485) (by norm_num)
theorem B2785877 : Blo 1156638 2785877 := bbase (se 8 (by rfl) ⟨16323, by rfl⟩ : syracuseStep 2785877 = 32647) (by norm_num)
theorem B1737317 : Blo 1156638 1737317 := bbase (se 4 (by rfl) ⟨162873, by rfl⟩ : syracuseStep 1737317 = 325747) (by norm_num)
theorem B1737341 : Blo 1156638 1737341 := bbase (se 3 (by rfl) ⟨325751, by rfl⟩ : syracuseStep 1737341 = 651503) (by norm_num)
theorem B1737365 : Blo 1156638 1737365 := bbase (se 6 (by rfl) ⟨40719, by rfl⟩ : syracuseStep 1737365 = 81439) (by norm_num)
theorem B1737389 : Blo 1156638 1737389 := bbase (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) (by norm_num)
theorem B6357685 : Blo 1156638 6357685 := bbase (se 5 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 6357685 = 596033) (by norm_num)
theorem B1737413 : Blo 1156638 1737413 := bbase (se 4 (by rfl) ⟨162882, by rfl⟩ : syracuseStep 1737413 = 325765) (by norm_num)
theorem B5866181 : Blo 1156638 5866181 := bbase (se 4 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 5866181 = 1099909) (by norm_num)
theorem B2196173 : Blo 1156638 2196173 := bbase (se 3 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 2196173 = 823565) (by norm_num)
theorem B1737437 : Blo 1156638 1737437 := bbase (se 3 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 1737437 = 651539) (by norm_num)
theorem B1737461 : Blo 1156638 1737461 := bbase (se 5 (by rfl) ⟨81443, by rfl⟩ : syracuseStep 1737461 = 162887) (by norm_num)
theorem B1737485 : Blo 1156638 1737485 := bbase (se 3 (by rfl) ⟨325778, by rfl⟩ : syracuseStep 1737485 = 651557) (by norm_num)
theorem B7144213 : Blo 1156638 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B1737509 : Blo 1156638 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B1737533 : Blo 1156638 1737533 := bbase (se 3 (by rfl) ⟨325787, by rfl⟩ : syracuseStep 1737533 = 651575) (by norm_num)
theorem B1737557 : Blo 1156638 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B2196325 : Blo 1156638 2196325 := bbase (se 4 (by rfl) ⟨205905, by rfl⟩ : syracuseStep 2196325 = 411811) (by norm_num)
theorem B1737581 : Blo 1156638 1737581 := bbase (se 3 (by rfl) ⟨325796, by rfl⟩ : syracuseStep 1737581 = 651593) (by norm_num)
theorem B1737605 : Blo 1156638 1737605 := bbase (se 4 (by rfl) ⟨162900, by rfl⟩ : syracuseStep 1737605 = 325801) (by norm_num)
theorem B1737629 : Blo 1156638 1737629 := bbase (se 3 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 1737629 = 651611) (by norm_num)
theorem B2786221 : Blo 1156638 2786221 := bbase (se 3 (by rfl) ⟨522416, by rfl⟩ : syracuseStep 2786221 = 1044833) (by norm_num)
theorem B1737653 : Blo 1156638 1737653 := bbase (se 5 (by rfl) ⟨81452, by rfl⟩ : syracuseStep 1737653 = 162905) (by norm_num)
theorem B1737677 : Blo 1156638 1737677 := bbase (se 3 (by rfl) ⟨325814, by rfl⟩ : syracuseStep 1737677 = 651629) (by norm_num)
theorem B1737701 : Blo 1156638 1737701 := bbase (se 4 (by rfl) ⟨162909, by rfl⟩ : syracuseStep 1737701 = 325819) (by norm_num)
theorem B1737725 : Blo 1156638 1737725 := bbase (se 3 (by rfl) ⟨325823, by rfl⟩ : syracuseStep 1737725 = 651647) (by norm_num)
theorem B1737749 : Blo 1156638 1737749 := bbase (se 6 (by rfl) ⟨40728, by rfl⟩ : syracuseStep 1737749 = 81457) (by norm_num)
theorem B1672213 : Blo 1156638 1672213 := bbase (se 6 (by rfl) ⟨39192, by rfl⟩ : syracuseStep 1672213 = 78385) (by norm_num)
theorem B1737773 : Blo 1156638 1737773 := bbase (se 3 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 1737773 = 651665) (by norm_num)
theorem B4949045 : Blo 1156638 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B11142197 : Blo 1156638 11142197 := bbase (se 5 (by rfl) ⟨522290, by rfl⟩ : syracuseStep 11142197 = 1044581) (by norm_num)
theorem B1737797 : Blo 1156638 1737797 := bbase (se 4 (by rfl) ⟨162918, by rfl⟩ : syracuseStep 1737797 = 325837) (by norm_num)
theorem B1737821 : Blo 1156638 1737821 := bbase (se 3 (by rfl) ⟨325841, by rfl⟩ : syracuseStep 1737821 = 651683) (by norm_num)
theorem B1737845 : Blo 1156638 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B1737869 : Blo 1156638 1737869 := bbase (se 3 (by rfl) ⟨325850, by rfl⟩ : syracuseStep 1737869 = 651701) (by norm_num)
theorem B2196629 : Blo 1156638 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B2786453 : Blo 1156638 2786453 := bbase (se 6 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 2786453 = 130615) (by norm_num)
theorem B1737893 : Blo 1156638 1737893 := bbase (se 4 (by rfl) ⟨162927, by rfl⟩ : syracuseStep 1737893 = 325855) (by norm_num)
theorem B1737917 : Blo 1156638 1737917 := bbase (se 3 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 1737917 = 651719) (by norm_num)
theorem B1737941 : Blo 1156638 1737941 := bbase (se 7 (by rfl) ⟨20366, by rfl⟩ : syracuseStep 1737941 = 40733) (by norm_num)
theorem B1737965 : Blo 1156638 1737965 := bbase (se 3 (by rfl) ⟨325868, by rfl⟩ : syracuseStep 1737965 = 651737) (by norm_num)
theorem B1737989 : Blo 1156638 1737989 := bbase (se 4 (by rfl) ⟨162936, by rfl⟩ : syracuseStep 1737989 = 325873) (by norm_num)
theorem B1738013 : Blo 1156638 1738013 := bbase (se 3 (by rfl) ⟨325877, by rfl⟩ : syracuseStep 1738013 = 651755) (by norm_num)
theorem B1738037 : Blo 1156638 1738037 := bbase (se 5 (by rfl) ⟨81470, by rfl⟩ : syracuseStep 1738037 = 162941) (by norm_num)
theorem B3343685 : Blo 1156638 3343685 := bbase (se 4 (by rfl) ⟨313470, by rfl⟩ : syracuseStep 3343685 = 626941) (by norm_num)
theorem B1738061 : Blo 1156638 1738061 := bbase (se 3 (by rfl) ⟨325886, by rfl⟩ : syracuseStep 1738061 = 651773) (by norm_num)
theorem B2786645 : Blo 1156638 2786645 := bbase (se 12 (by rfl) ⟨1020, by rfl⟩ : syracuseStep 2786645 = 2041) (by norm_num)
theorem B1738085 : Blo 1156638 1738085 := bbase (se 4 (by rfl) ⟨162945, by rfl⟩ : syracuseStep 1738085 = 325891) (by norm_num)
theorem B1738109 : Blo 1156638 1738109 := bbase (se 3 (by rfl) ⟨325895, by rfl⟩ : syracuseStep 1738109 = 651791) (by norm_num)
theorem B1738133 : Blo 1156638 1738133 := bbase (se 6 (by rfl) ⟨40737, by rfl⟩ : syracuseStep 1738133 = 81475) (by norm_num)
theorem B1738157 : Blo 1156638 1738157 := bbase (se 3 (by rfl) ⟨325904, by rfl⟩ : syracuseStep 1738157 = 651809) (by norm_num)
theorem B1410481 : Blo 1156638 1410481 := bbase (se 2 (by rfl) ⟨528930, by rfl⟩ : syracuseStep 1410481 = 1057861) (by norm_num)
theorem B1738181 : Blo 1156638 1738181 := bbase (se 4 (by rfl) ⟨162954, by rfl⟩ : syracuseStep 1738181 = 325909) (by norm_num)
theorem B1738205 : Blo 1156638 1738205 := bbase (se 3 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 1738205 = 651827) (by norm_num)
theorem B1738229 : Blo 1156638 1738229 := bbase (se 5 (by rfl) ⟨81479, by rfl⟩ : syracuseStep 1738229 = 162959) (by norm_num)
theorem B1738253 : Blo 1156638 1738253 := bbase (se 3 (by rfl) ⟨325922, by rfl⟩ : syracuseStep 1738253 = 651845) (by norm_num)
theorem B1738277 : Blo 1156638 1738277 := bbase (se 4 (by rfl) ⟨162963, by rfl⟩ : syracuseStep 1738277 = 325927) (by norm_num)
theorem B1738301 : Blo 1156638 1738301 := bbase (se 3 (by rfl) ⟨325931, by rfl⟩ : syracuseStep 1738301 = 651863) (by norm_num)
theorem B1738325 : Blo 1156638 1738325 := bbase (se 8 (by rfl) ⟨10185, by rfl⟩ : syracuseStep 1738325 = 20371) (by norm_num)
theorem B1738349 : Blo 1156638 1738349 := bbase (se 3 (by rfl) ⟨325940, by rfl⟩ : syracuseStep 1738349 = 651881) (by norm_num)
theorem B8783477 : Blo 1156638 8783477 := bbase (se 5 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 8783477 = 823451) (by norm_num)
theorem B2786933 : Blo 1156638 2786933 := bbase (se 5 (by rfl) ⟨130637, by rfl⟩ : syracuseStep 2786933 = 261275) (by norm_num)
theorem B1738373 : Blo 1156638 1738373 := bbase (se 4 (by rfl) ⟨162972, by rfl⟩ : syracuseStep 1738373 = 325945) (by norm_num)
theorem B1738397 : Blo 1156638 1738397 := bbase (se 3 (by rfl) ⟨325949, by rfl⟩ : syracuseStep 1738397 = 651899) (by norm_num)
theorem B1738421 : Blo 1156638 1738421 := bbase (se 5 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 1738421 = 162977) (by norm_num)
theorem B1738445 : Blo 1156638 1738445 := bbase (se 3 (by rfl) ⟨325958, by rfl⟩ : syracuseStep 1738445 = 651917) (by norm_num)
theorem B8914645 : Blo 1156638 8914645 := bbase (se 7 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 8914645 = 208937) (by norm_num)
theorem B1738469 : Blo 1156638 1738469 := bbase (se 4 (by rfl) ⟨162981, by rfl⟩ : syracuseStep 1738469 = 325963) (by norm_num)
theorem B1738493 : Blo 1156638 1738493 := bbase (se 3 (by rfl) ⟨325967, by rfl⟩ : syracuseStep 1738493 = 651935) (by norm_num)
theorem B1738517 : Blo 1156638 1738517 := bbase (se 6 (by rfl) ⟨40746, by rfl⟩ : syracuseStep 1738517 = 81493) (by norm_num)
theorem B1738541 : Blo 1156638 1738541 := bbase (se 3 (by rfl) ⟨325976, by rfl⟩ : syracuseStep 1738541 = 651953) (by norm_num)
theorem B1738565 : Blo 1156638 1738565 := bbase (se 4 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 1738565 = 325981) (by norm_num)
theorem B1738589 : Blo 1156638 1738589 := bbase (se 3 (by rfl) ⟨325985, by rfl⟩ : syracuseStep 1738589 = 651971) (by norm_num)
theorem B1738613 : Blo 1156638 1738613 := bbase (se 5 (by rfl) ⟨81497, by rfl⟩ : syracuseStep 1738613 = 162995) (by norm_num)
theorem B2197381 : Blo 1156638 2197381 := bbase (se 4 (by rfl) ⟨206004, by rfl⟩ : syracuseStep 2197381 = 412009) (by norm_num)
theorem B1738637 : Blo 1156638 1738637 := bbase (se 3 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 1738637 = 651989) (by norm_num)
theorem B21170069 : Blo 1156638 21170069 := bbase (se 6 (by rfl) ⟨496173, by rfl⟩ : syracuseStep 21170069 = 992347) (by norm_num)
theorem B1738661 : Blo 1156638 1738661 := bbase (se 4 (by rfl) ⟨162999, by rfl⟩ : syracuseStep 1738661 = 325999) (by norm_num)
theorem B1738685 : Blo 1156638 1738685 := bbase (se 3 (by rfl) ⟨326003, by rfl⟩ : syracuseStep 1738685 = 652007) (by norm_num)
theorem B5867477 : Blo 1156638 5867477 := bbase (se 7 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 5867477 = 137519) (by norm_num)
theorem B1738709 : Blo 1156638 1738709 := bbase (se 7 (by rfl) ⟨20375, by rfl⟩ : syracuseStep 1738709 = 40751) (by norm_num)
theorem B1738733 : Blo 1156638 1738733 := bbase (se 3 (by rfl) ⟨326012, by rfl⟩ : syracuseStep 1738733 = 652025) (by norm_num)
theorem B5572597 : Blo 1156638 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B1738757 : Blo 1156638 1738757 := bbase (se 4 (by rfl) ⟨163008, by rfl⟩ : syracuseStep 1738757 = 326017) (by norm_num)
theorem B2197525 : Blo 1156638 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B1738781 : Blo 1156638 1738781 := bbase (se 3 (by rfl) ⟨326021, by rfl⟩ : syracuseStep 1738781 = 652043) (by norm_num)
theorem B1738805 : Blo 1156638 1738805 := bbase (se 5 (by rfl) ⟨81506, by rfl⟩ : syracuseStep 1738805 = 163013) (by norm_num)
theorem B1738829 : Blo 1156638 1738829 := bbase (se 3 (by rfl) ⟨326030, by rfl⟩ : syracuseStep 1738829 = 652061) (by norm_num)
theorem B4393061 : Blo 1156638 4393061 := bbase (se 4 (by rfl) ⟨411849, by rfl⟩ : syracuseStep 4393061 = 823699) (by norm_num)
theorem B1738853 : Blo 1156638 1738853 := bbase (se 4 (by rfl) ⟨163017, by rfl⟩ : syracuseStep 1738853 = 326035) (by norm_num)
theorem B1738877 : Blo 1156638 1738877 := bbase (se 3 (by rfl) ⟨326039, by rfl⟩ : syracuseStep 1738877 = 652079) (by norm_num)
theorem B1738901 : Blo 1156638 1738901 := bbase (se 6 (by rfl) ⟨40755, by rfl⟩ : syracuseStep 1738901 = 81511) (by norm_num)
theorem B1738925 : Blo 1156638 1738925 := bbase (se 3 (by rfl) ⟨326048, by rfl⟩ : syracuseStep 1738925 = 652097) (by norm_num)
theorem B2197685 : Blo 1156638 2197685 := bbase (se 5 (by rfl) ⟨103016, by rfl⟩ : syracuseStep 2197685 = 206033) (by norm_num)
theorem B1738949 : Blo 1156638 1738949 := bbase (se 4 (by rfl) ⟨163026, by rfl⟩ : syracuseStep 1738949 = 326053) (by norm_num)
theorem B1738973 : Blo 1156638 1738973 := bbase (se 3 (by rfl) ⟨326057, by rfl⟩ : syracuseStep 1738973 = 652115) (by norm_num)
theorem B1738997 : Blo 1156638 1738997 := bbase (se 5 (by rfl) ⟨81515, by rfl⟩ : syracuseStep 1738997 = 163031) (by norm_num)
theorem B1739021 : Blo 1156638 1739021 := bbase (se 3 (by rfl) ⟨326066, by rfl⟩ : syracuseStep 1739021 = 652133) (by norm_num)
theorem B1739045 : Blo 1156638 1739045 := bbase (se 4 (by rfl) ⟨163035, by rfl⟩ : syracuseStep 1739045 = 326071) (by norm_num)
theorem B1739069 : Blo 1156638 1739069 := bbase (se 3 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 1739069 = 652151) (by norm_num)
theorem B2197829 : Blo 1156638 2197829 := bbase (se 4 (by rfl) ⟨206046, by rfl⟩ : syracuseStep 2197829 = 412093) (by norm_num)
theorem B1739093 : Blo 1156638 1739093 := bbase (se 10 (by rfl) ⟨2547, by rfl⟩ : syracuseStep 1739093 = 5095) (by norm_num)
theorem B1739117 : Blo 1156638 1739117 := bbase (se 3 (by rfl) ⟨326084, by rfl⟩ : syracuseStep 1739117 = 652169) (by norm_num)
theorem B4393349 : Blo 1156638 4393349 := bbase (se 4 (by rfl) ⟨411876, by rfl⟩ : syracuseStep 4393349 = 823753) (by norm_num)
theorem B1739141 : Blo 1156638 1739141 := bbase (se 4 (by rfl) ⟨163044, by rfl⟩ : syracuseStep 1739141 = 326089) (by norm_num)
theorem B1739165 : Blo 1156638 1739165 := bbase (se 3 (by rfl) ⟨326093, by rfl⟩ : syracuseStep 1739165 = 652187) (by norm_num)
theorem B1739189 : Blo 1156638 1739189 := bbase (se 5 (by rfl) ⟨81524, by rfl⟩ : syracuseStep 1739189 = 163049) (by norm_num)
theorem B1739213 : Blo 1156638 1739213 := bbase (se 3 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 1739213 = 652205) (by norm_num)
theorem B13208021 : Blo 1156638 13208021 := bbase (se 7 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 13208021 = 309563) (by norm_num)
theorem B1739237 : Blo 1156638 1739237 := bbase (se 4 (by rfl) ⟨163053, by rfl⟩ : syracuseStep 1739237 = 326107) (by norm_num)
theorem B1739261 : Blo 1156638 1739261 := bbase (se 3 (by rfl) ⟨326111, by rfl⟩ : syracuseStep 1739261 = 652223) (by norm_num)
theorem B1739285 : Blo 1156638 1739285 := bbase (se 6 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 1739285 = 81529) (by norm_num)
theorem B1739309 : Blo 1156638 1739309 := bbase (se 3 (by rfl) ⟨326120, by rfl⟩ : syracuseStep 1739309 = 652241) (by norm_num)
theorem B1739333 : Blo 1156638 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B1739357 : Blo 1156638 1739357 := bbase (se 3 (by rfl) ⟨326129, by rfl⟩ : syracuseStep 1739357 = 652259) (by norm_num)
theorem B2198117 : Blo 1156638 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B1739381 : Blo 1156638 1739381 := bbase (se 5 (by rfl) ⟨81533, by rfl⟩ : syracuseStep 1739381 = 163067) (by norm_num)
theorem B1739405 : Blo 1156638 1739405 := bbase (se 3 (by rfl) ⟨326138, by rfl⟩ : syracuseStep 1739405 = 652277) (by norm_num)
theorem B5638805 : Blo 1156638 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B1739429 : Blo 1156638 1739429 := bbase (se 4 (by rfl) ⟨163071, by rfl⟩ : syracuseStep 1739429 = 326143) (by norm_num)
theorem B1739453 : Blo 1156638 1739453 := bbase (se 3 (by rfl) ⟨326147, by rfl⟩ : syracuseStep 1739453 = 652295) (by norm_num)
theorem B1739477 : Blo 1156638 1739477 := bbase (se 7 (by rfl) ⟨20384, by rfl⟩ : syracuseStep 1739477 = 40769) (by norm_num)
theorem B1739501 : Blo 1156638 1739501 := bbase (se 3 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 1739501 = 652313) (by norm_num)
theorem B2198269 : Blo 1156638 2198269 := bbase (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) (by norm_num)
theorem B1739525 : Blo 1156638 1739525 := bbase (se 4 (by rfl) ⟨163080, by rfl⟩ : syracuseStep 1739525 = 326161) (by norm_num)
theorem B1739549 : Blo 1156638 1739549 := bbase (se 3 (by rfl) ⟨326165, by rfl⟩ : syracuseStep 1739549 = 652331) (by norm_num)
theorem B4950821 : Blo 1156638 4950821 := bbase (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) (by norm_num)
theorem B1739573 : Blo 1156638 1739573 := bbase (se 5 (by rfl) ⟨81542, by rfl⟩ : syracuseStep 1739573 = 163085) (by norm_num)
theorem B1739597 : Blo 1156638 1739597 := bbase (se 3 (by rfl) ⟨326174, by rfl⟩ : syracuseStep 1739597 = 652349) (by norm_num)
theorem B1739621 : Blo 1156638 1739621 := bbase (se 4 (by rfl) ⟨163089, by rfl⟩ : syracuseStep 1739621 = 326179) (by norm_num)
theorem B1739645 : Blo 1156638 1739645 := bbase (se 3 (by rfl) ⟨326183, by rfl⟩ : syracuseStep 1739645 = 652367) (by norm_num)
theorem B1739669 : Blo 1156638 1739669 := bbase (se 6 (by rfl) ⟨40773, by rfl⟩ : syracuseStep 1739669 = 81547) (by norm_num)
theorem B1739693 : Blo 1156638 1739693 := bbase (se 3 (by rfl) ⟨326192, by rfl⟩ : syracuseStep 1739693 = 652385) (by norm_num)
theorem B1739717 : Blo 1156638 1739717 := bbase (se 4 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 1739717 = 326197) (by norm_num)
theorem B1739741 : Blo 1156638 1739741 := bbase (se 3 (by rfl) ⟨326201, by rfl⟩ : syracuseStep 1739741 = 652403) (by norm_num)
theorem B1739765 : Blo 1156638 1739765 := bbase (se 5 (by rfl) ⟨81551, by rfl⟩ : syracuseStep 1739765 = 163103) (by norm_num)
theorem B1739789 : Blo 1156638 1739789 := bbase (se 3 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 1739789 = 652421) (by norm_num)
theorem B1739813 : Blo 1156638 1739813 := bbase (se 4 (by rfl) ⟨163107, by rfl⟩ : syracuseStep 1739813 = 326215) (by norm_num)
theorem B2198573 : Blo 1156638 2198573 := bbase (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) (by norm_num)
theorem B1739837 : Blo 1156638 1739837 := bbase (se 3 (by rfl) ⟨326219, by rfl⟩ : syracuseStep 1739837 = 652439) (by norm_num)
theorem B1739861 : Blo 1156638 1739861 := bbase (se 8 (by rfl) ⟨10194, by rfl⟩ : syracuseStep 1739861 = 20389) (by norm_num)
theorem B1739885 : Blo 1156638 1739885 := bbase (se 3 (by rfl) ⟨326228, by rfl⟩ : syracuseStep 1739885 = 652457) (by norm_num)
theorem B1739909 : Blo 1156638 1739909 := bbase (se 4 (by rfl) ⟨163116, by rfl⟩ : syracuseStep 1739909 = 326233) (by norm_num)
theorem B1739933 : Blo 1156638 1739933 := bbase (se 3 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 1739933 = 652475) (by norm_num)
theorem B1739957 : Blo 1156638 1739957 := bbase (se 5 (by rfl) ⟨81560, by rfl⟩ : syracuseStep 1739957 = 163121) (by norm_num)
theorem B1739981 : Blo 1156638 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B3706069 : Blo 1156638 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B5868773 : Blo 1156638 5868773 := bbase (se 4 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 5868773 = 1100395) (by norm_num)
theorem B1740005 : Blo 1156638 1740005 := bbase (se 4 (by rfl) ⟨163125, by rfl⟩ : syracuseStep 1740005 = 326251) (by norm_num)
theorem B1740029 : Blo 1156638 1740029 := bbase (se 3 (by rfl) ⟨326255, by rfl⟩ : syracuseStep 1740029 = 652511) (by norm_num)
theorem B1740053 : Blo 1156638 1740053 := bbase (se 6 (by rfl) ⟨40782, by rfl⟩ : syracuseStep 1740053 = 81565) (by norm_num)
theorem B1740077 : Blo 1156638 1740077 := bbase (se 3 (by rfl) ⟨326264, by rfl⟩ : syracuseStep 1740077 = 652529) (by norm_num)
theorem B1740101 : Blo 1156638 1740101 := bbase (se 4 (by rfl) ⟨163134, by rfl⟩ : syracuseStep 1740101 = 326269) (by norm_num)
theorem B1740125 : Blo 1156638 1740125 := bbase (se 3 (by rfl) ⟨326273, by rfl⟩ : syracuseStep 1740125 = 652547) (by norm_num)
theorem B1740149 : Blo 1156638 1740149 := bbase (se 5 (by rfl) ⟨81569, by rfl⟩ : syracuseStep 1740149 = 163139) (by norm_num)
theorem B1740173 : Blo 1156638 1740173 := bbase (se 3 (by rfl) ⟨326282, by rfl⟩ : syracuseStep 1740173 = 652565) (by norm_num)
theorem B1740197 : Blo 1156638 1740197 := bbase (se 4 (by rfl) ⟨163143, by rfl⟩ : syracuseStep 1740197 = 326287) (by norm_num)
theorem B1740221 : Blo 1156638 1740221 := bbase (se 3 (by rfl) ⟨326291, by rfl⟩ : syracuseStep 1740221 = 652583) (by norm_num)
theorem B6032837 : Blo 1156638 6032837 := bbase (se 4 (by rfl) ⟨565578, by rfl⟩ : syracuseStep 6032837 = 1131157) (by norm_num)
theorem B1740245 : Blo 1156638 1740245 := bbase (se 7 (by rfl) ⟨20393, by rfl⟩ : syracuseStep 1740245 = 40787) (by norm_num)
theorem B1740269 : Blo 1156638 1740269 := bbase (se 3 (by rfl) ⟨326300, by rfl⟩ : syracuseStep 1740269 = 652601) (by norm_num)
theorem B1412597 : Blo 1156638 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B1740293 : Blo 1156638 1740293 := bbase (se 4 (by rfl) ⟨163152, by rfl⟩ : syracuseStep 1740293 = 326305) (by norm_num)
theorem B1740317 : Blo 1156638 1740317 := bbase (se 3 (by rfl) ⟨326309, by rfl⟩ : syracuseStep 1740317 = 652619) (by norm_num)
theorem B4394533 : Blo 1156638 4394533 := bbase (se 4 (by rfl) ⟨411987, by rfl⟩ : syracuseStep 4394533 = 823975) (by norm_num)
theorem B1740341 : Blo 1156638 1740341 := bbase (se 5 (by rfl) ⟨81578, by rfl⟩ : syracuseStep 1740341 = 163157) (by norm_num)
theorem B1740365 : Blo 1156638 1740365 := bbase (se 3 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 1740365 = 652637) (by norm_num)
theorem B1740389 : Blo 1156638 1740389 := bbase (se 4 (by rfl) ⟨163161, by rfl⟩ : syracuseStep 1740389 = 326323) (by norm_num)
theorem B6590069 : Blo 1156638 6590069 := bbase (se 5 (by rfl) ⟨308909, by rfl⟩ : syracuseStep 6590069 = 617819) (by norm_num)
theorem B1740413 : Blo 1156638 1740413 := bbase (se 3 (by rfl) ⟨326327, by rfl⟩ : syracuseStep 1740413 = 652655) (by norm_num)
theorem B1740437 : Blo 1156638 1740437 := bbase (se 6 (by rfl) ⟨40791, by rfl⟩ : syracuseStep 1740437 = 81583) (by norm_num)
theorem B1740461 : Blo 1156638 1740461 := bbase (se 3 (by rfl) ⟨326336, by rfl⟩ : syracuseStep 1740461 = 652673) (by norm_num)
theorem B1740485 : Blo 1156638 1740485 := bbase (se 4 (by rfl) ⟨163170, by rfl⟩ : syracuseStep 1740485 = 326341) (by norm_num)
theorem B1740509 : Blo 1156638 1740509 := bbase (se 3 (by rfl) ⟨326345, by rfl⟩ : syracuseStep 1740509 = 652691) (by norm_num)
theorem B1740533 : Blo 1156638 1740533 := bbase (se 5 (by rfl) ⟨81587, by rfl⟩ : syracuseStep 1740533 = 163175) (by norm_num)
theorem B4951813 : Blo 1156638 4951813 := bbase (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) (by norm_num)
theorem B1740557 : Blo 1156638 1740557 := bbase (se 3 (by rfl) ⟨326354, by rfl⟩ : syracuseStep 1740557 = 652709) (by norm_num)
theorem B2199325 : Blo 1156638 2199325 := bbase (se 3 (by rfl) ⟨412373, by rfl⟩ : syracuseStep 2199325 = 824747) (by norm_num)
theorem B1740581 : Blo 1156638 1740581 := bbase (se 4 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 1740581 = 326359) (by norm_num)
theorem B1740605 : Blo 1156638 1740605 := bbase (se 3 (by rfl) ⟨326363, by rfl⟩ : syracuseStep 1740605 = 652727) (by norm_num)
theorem B4394837 : Blo 1156638 4394837 := bbase (se 9 (by rfl) ⟨12875, by rfl⟩ : syracuseStep 4394837 = 25751) (by norm_num)
theorem B1740629 : Blo 1156638 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1740653 : Blo 1156638 1740653 := bbase (se 3 (by rfl) ⟨326372, by rfl⟩ : syracuseStep 1740653 = 652745) (by norm_num)
theorem B1740677 : Blo 1156638 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B1740701 : Blo 1156638 1740701 := bbase (se 3 (by rfl) ⟨326381, by rfl⟩ : syracuseStep 1740701 = 652763) (by norm_num)
theorem B2199469 : Blo 1156638 2199469 := bbase (se 3 (by rfl) ⟨412400, by rfl⟩ : syracuseStep 2199469 = 824801) (by norm_num)
theorem B1740725 : Blo 1156638 1740725 := bbase (se 5 (by rfl) ⟨81596, by rfl⟩ : syracuseStep 1740725 = 163193) (by norm_num)
theorem B1740749 : Blo 1156638 1740749 := bbase (se 3 (by rfl) ⟨326390, by rfl⟩ : syracuseStep 1740749 = 652781) (by norm_num)
theorem B1740773 : Blo 1156638 1740773 := bbase (se 4 (by rfl) ⟨163197, by rfl⟩ : syracuseStep 1740773 = 326395) (by norm_num)
theorem B1740797 : Blo 1156638 1740797 := bbase (se 3 (by rfl) ⟨326399, by rfl⟩ : syracuseStep 1740797 = 652799) (by norm_num)
theorem B1740821 : Blo 1156638 1740821 := bbase (se 6 (by rfl) ⟨40800, by rfl⟩ : syracuseStep 1740821 = 81601) (by norm_num)
theorem B1740845 : Blo 1156638 1740845 := bbase (se 3 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 1740845 = 652817) (by norm_num)
theorem B1740869 : Blo 1156638 1740869 := bbase (se 4 (by rfl) ⟨163206, by rfl⟩ : syracuseStep 1740869 = 326413) (by norm_num)
theorem B2199629 : Blo 1156638 2199629 := bbase (se 3 (by rfl) ⟨412430, by rfl⟩ : syracuseStep 2199629 = 824861) (by norm_num)
theorem B1740893 : Blo 1156638 1740893 := bbase (se 3 (by rfl) ⟨326417, by rfl⟩ : syracuseStep 1740893 = 652835) (by norm_num)
theorem B1740917 : Blo 1156638 1740917 := bbase (se 5 (by rfl) ⟨81605, by rfl⟩ : syracuseStep 1740917 = 163211) (by norm_num)
theorem B1740941 : Blo 1156638 1740941 := bbase (se 3 (by rfl) ⟨326426, by rfl⟩ : syracuseStep 1740941 = 652853) (by norm_num)
theorem B2199773 : Blo 1156638 2199773 := bbase (se 3 (by rfl) ⟨412457, by rfl⟩ : syracuseStep 2199773 = 824915) (by norm_num)
theorem B4526533 : Blo 1156638 4526533 := bbase (se 4 (by rfl) ⟨424362, by rfl⟩ : syracuseStep 4526533 = 848725) (by norm_num)
theorem B5870069 : Blo 1156638 5870069 := bbase (se 5 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 5870069 = 550319) (by norm_num)
theorem B2200061 : Blo 1156638 2200061 := bbase (se 3 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 2200061 = 825023) (by norm_num)
theorem B21172757 : Blo 1156638 21172757 := bbase (se 6 (by rfl) ⟨496236, by rfl⟩ : syracuseStep 21172757 = 992473) (by norm_num)
theorem B3904037 : Blo 1156638 3904037 := bbase (se 4 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 3904037 = 732007) (by norm_num)
theorem B2200213 : Blo 1156638 2200213 := bbase (se 6 (by rfl) ⟨51567, by rfl⟩ : syracuseStep 2200213 = 103135) (by norm_num)
theorem B6591253 : Blo 1156638 6591253 := bbase (se 6 (by rfl) ⟨154482, by rfl⟩ : syracuseStep 6591253 = 308965) (by norm_num)
theorem B2200517 : Blo 1156638 2200517 := bbase (se 4 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 2200517 = 412597) (by norm_num)
theorem B3904469 : Blo 1156638 3904469 := bbase (se 7 (by rfl) ⟨45755, by rfl⟩ : syracuseStep 3904469 = 91511) (by norm_num)
theorem B7050581 : Blo 1156638 7050581 := bbase (se 14 (by rfl) ⟨645, by rfl⟩ : syracuseStep 7050581 = 1291) (by norm_num)
theorem B3904901 : Blo 1156638 3904901 := bbase (se 4 (by rfl) ⟨366084, by rfl⟩ : syracuseStep 3904901 = 732169) (by norm_num)
theorem B2201269 : Blo 1156638 2201269 := bbase (se 5 (by rfl) ⟨103184, by rfl⟩ : syracuseStep 2201269 = 206369) (by norm_num)
theorem B4888325 : Blo 1156638 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B5871365 : Blo 1156638 5871365 := bbase (se 4 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 5871365 = 1100881) (by norm_num)
theorem B3905333 : Blo 1156638 3905333 := bbase (se 5 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 3905333 = 366125) (by norm_num)
theorem B2201413 : Blo 1156638 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B4396949 : Blo 1156638 4396949 := bbase (se 6 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 4396949 = 206107) (by norm_num)
theorem B2201573 : Blo 1156638 2201573 := bbase (se 4 (by rfl) ⟨206397, by rfl⟩ : syracuseStep 2201573 = 412795) (by norm_num)
theorem B3708965 : Blo 1156638 3708965 := bbase (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) (by norm_num)
theorem B12064853 : Blo 1156638 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B5576789 : Blo 1156638 5576789 := bbase (se 8 (by rfl) ⟨32676, by rfl⟩ : syracuseStep 5576789 = 65353) (by norm_num)
theorem B2201717 : Blo 1156638 2201717 := bbase (se 5 (by rfl) ⟨103205, by rfl⟩ : syracuseStep 2201717 = 206411) (by norm_num)
theorem B4397237 : Blo 1156638 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B3905765 : Blo 1156638 3905765 := bbase (se 4 (by rfl) ⟨366165, by rfl⟩ : syracuseStep 3905765 = 732331) (by norm_num)
theorem B4692277 : Blo 1156638 4692277 := bbase (se 5 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 4692277 = 439901) (by norm_num)
theorem B2202005 : Blo 1156638 2202005 := bbase (se 6 (by rfl) ⟨51609, by rfl⟩ : syracuseStep 2202005 = 103219) (by norm_num)
theorem B2202157 : Blo 1156638 2202157 := bbase (se 3 (by rfl) ⟨412904, by rfl⟩ : syracuseStep 2202157 = 825809) (by norm_num)
theorem B3906197 : Blo 1156638 3906197 := bbase (se 6 (by rfl) ⟨91551, by rfl⟩ : syracuseStep 3906197 = 183103) (by norm_num)
theorem B6593237 : Blo 1156638 6593237 := bbase (se 7 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 6593237 = 154529) (by norm_num)
theorem B2202461 : Blo 1156638 2202461 := bbase (se 3 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 2202461 = 825923) (by norm_num)
theorem B5872661 : Blo 1156638 5872661 := bbase (se 6 (by rfl) ⟨137640, by rfl⟩ : syracuseStep 5872661 = 275281) (by norm_num)
theorem B3906629 : Blo 1156638 3906629 := bbase (se 4 (by rfl) ⟨366246, by rfl⟩ : syracuseStep 3906629 = 732493) (by norm_num)
theorem B38083925 : Blo 1156638 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B4398421 : Blo 1156638 4398421 := bbase (se 11 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 4398421 = 6443) (by norm_num)
theorem B4693445 : Blo 1156638 4693445 := bbase (se 4 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 4693445 = 880021) (by norm_num)
theorem B3907061 : Blo 1156638 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B2203213 : Blo 1156638 2203213 := bbase (se 3 (by rfl) ⟨413102, by rfl⟩ : syracuseStep 2203213 = 826205) (by norm_num)
theorem B4398725 : Blo 1156638 4398725 := bbase (se 4 (by rfl) ⟨412380, by rfl⟩ : syracuseStep 4398725 = 824761) (by norm_num)
theorem B4169413 : Blo 1156638 4169413 := bbase (se 4 (by rfl) ⟨390882, by rfl⟩ : syracuseStep 4169413 = 781765) (by norm_num)
theorem B9903829 : Blo 1156638 9903829 := bbase (se 7 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 9903829 = 232121) (by norm_num)
theorem B2203357 : Blo 1156638 2203357 := bbase (se 3 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 2203357 = 826259) (by norm_num)
theorem B3907493 : Blo 1156638 3907493 := bbase (se 4 (by rfl) ⟨366327, by rfl⟩ : syracuseStep 3907493 = 732655) (by norm_num)
theorem B3711221 : Blo 1156638 3711221 := bbase (se 5 (by rfl) ⟨173963, by rfl⟩ : syracuseStep 3711221 = 347927) (by norm_num)
theorem B5873957 : Blo 1156638 5873957 := bbase (se 4 (by rfl) ⟨550683, by rfl⟩ : syracuseStep 5873957 = 1101367) (by norm_num)
theorem B3907925 : Blo 1156638 3907925 := bbase (se 10 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 3907925 = 11449) (by norm_num)
theorem B4170325 : Blo 1156638 4170325 := bbase (se 8 (by rfl) ⟨24435, by rfl⟩ : syracuseStep 4170325 = 48871) (by norm_num)
theorem B1647221 : Blo 1156638 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B4956821 : Blo 1156638 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B3908357 : Blo 1156638 3908357 := bbase (se 4 (by rfl) ⟨366408, by rfl⟩ : syracuseStep 3908357 = 732817) (by norm_num)
theorem B6595445 : Blo 1156638 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B4957109 : Blo 1156638 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B3711989 : Blo 1156638 3711989 := bbase (se 5 (by rfl) ⟨173999, by rfl⟩ : syracuseStep 3711989 = 347999) (by norm_num)
theorem B1254485 : Blo 1156638 1254485 := bbase (se 8 (by rfl) ⟨7350, by rfl⟩ : syracuseStep 1254485 = 14701) (by norm_num)
theorem B5022805 : Blo 1156638 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B3908789 : Blo 1156638 3908789 := bbase (se 5 (by rfl) ⟨183224, by rfl⟩ : syracuseStep 3908789 = 366449) (by norm_num)
theorem B8791253 : Blo 1156638 8791253 := bbase (se 7 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 8791253 = 206045) (by norm_num)
theorem B1254637 : Blo 1156638 1254637 := bbase (se 3 (by rfl) ⟨235244, by rfl⟩ : syracuseStep 1254637 = 470489) (by norm_num)
theorem B1647973 : Blo 1156638 1647973 := bbase (se 4 (by rfl) ⟨154497, by rfl⟩ : syracuseStep 1647973 = 308995) (by norm_num)
theorem B2860397 : Blo 1156638 2860397 := bbase (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) (by norm_num)
theorem B2860469 : Blo 1156638 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B3712501 : Blo 1156638 3712501 := bbase (se 5 (by rfl) ⟨174023, by rfl⟩ : syracuseStep 3712501 = 348047) (by norm_num)
theorem B5875253 : Blo 1156638 5875253 := bbase (se 5 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 5875253 = 550805) (by norm_num)
theorem B3909221 : Blo 1156638 3909221 := bbase (se 4 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 3909221 = 732979) (by norm_num)
theorem B9905813 : Blo 1156638 9905813 := bbase (se 6 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 9905813 = 464335) (by norm_num)
theorem B4400837 : Blo 1156638 4400837 := bbase (se 4 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 4400837 = 825157) (by norm_num)
theorem B1189601 : Blo 1156638 1189601 := bbase (se 2 (by rfl) ⟨446100, by rfl⟩ : syracuseStep 1189601 = 892201) (by norm_num)
theorem B1255213 : Blo 1156638 1255213 := bbase (se 3 (by rfl) ⟨235352, by rfl⟩ : syracuseStep 1255213 = 470705) (by norm_num)
theorem B4401125 : Blo 1156638 4401125 := bbase (se 4 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 4401125 = 825211) (by norm_num)
theorem B3909653 : Blo 1156638 3909653 := bbase (se 6 (by rfl) ⟨91632, by rfl⟩ : syracuseStep 3909653 = 183265) (by norm_num)
theorem B1648765 : Blo 1156638 1648765 := bbase (se 3 (by rfl) ⟨309143, by rfl⟩ : syracuseStep 1648765 = 618287) (by norm_num)
theorem B3910085 : Blo 1156638 3910085 := bbase (se 4 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 3910085 = 733141) (by norm_num)
theorem B1649101 : Blo 1156638 1649101 := bbase (se 3 (by rfl) ⟨309206, by rfl⟩ : syracuseStep 1649101 = 618413) (by norm_num)
theorem B1878565 : Blo 1156638 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1649317 : Blo 1156638 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B4696805 : Blo 1156638 4696805 := bbase (se 4 (by rfl) ⟨440325, by rfl⟩ : syracuseStep 4696805 = 880651) (by norm_num)
theorem B3910517 : Blo 1156638 3910517 := bbase (se 5 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 3910517 = 366611) (by norm_num)
theorem B6269845 : Blo 1156638 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B4172789 : Blo 1156638 4172789 := bbase (se 5 (by rfl) ⟨195599, by rfl⟩ : syracuseStep 4172789 = 391199) (by norm_num)
theorem B1649693 : Blo 1156638 1649693 := bbase (se 3 (by rfl) ⟨309317, by rfl⟩ : syracuseStep 1649693 = 618635) (by norm_num)
theorem B4172933 : Blo 1156638 4172933 := bbase (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) (by norm_num)
theorem B4402309 : Blo 1156638 4402309 := bbase (se 4 (by rfl) ⟨412716, by rfl⟩ : syracuseStep 4402309 = 825433) (by norm_num)
theorem B2927765 : Blo 1156638 2927765 := bbase (se 6 (by rfl) ⟨68619, by rfl⟩ : syracuseStep 2927765 = 137239) (by norm_num)
theorem B3714245 : Blo 1156638 3714245 := bbase (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) (by norm_num)
theorem B7417109 : Blo 1156638 7417109 := bbase (se 6 (by rfl) ⟨173838, by rfl⟩ : syracuseStep 7417109 = 347677) (by norm_num)
theorem B3910949 : Blo 1156638 3910949 := bbase (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) (by norm_num)
theorem B3714437 : Blo 1156638 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B18787733 : Blo 1156638 18787733 := bbase (se 6 (by rfl) ⟨440337, by rfl⟩ : syracuseStep 18787733 = 880675) (by norm_num)
theorem B1486237 : Blo 1156638 1486237 := bbase (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) (by norm_num)
theorem B4173221 : Blo 1156638 4173221 := bbase (se 4 (by rfl) ⟨391239, by rfl⟩ : syracuseStep 4173221 = 782479) (by norm_num)
theorem B4402613 : Blo 1156638 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B2928109 : Blo 1156638 2928109 := bbase (se 3 (by rfl) ⟨549020, by rfl⟩ : syracuseStep 2928109 = 1098041) (by norm_num)
theorem B2928221 : Blo 1156638 2928221 := bbase (se 3 (by rfl) ⟨549041, by rfl⟩ : syracuseStep 2928221 = 1098083) (by norm_num)
theorem B3911381 : Blo 1156638 3911381 := bbase (se 7 (by rfl) ⟨45836, by rfl⟩ : syracuseStep 3911381 = 91673) (by norm_num)
theorem B5713669 : Blo 1156638 5713669 := bbase (se 4 (by rfl) ⟨535656, by rfl⟩ : syracuseStep 5713669 = 1071313) (by norm_num)
theorem B2928413 : Blo 1156638 2928413 := bbase (se 3 (by rfl) ⟨549077, by rfl⟩ : syracuseStep 2928413 = 1098155) (by norm_num)
theorem B4698053 : Blo 1156638 4698053 := bbase (se 4 (by rfl) ⟨440442, by rfl⟩ : syracuseStep 4698053 = 880885) (by norm_num)
theorem B2928757 : Blo 1156638 2928757 := bbase (se 5 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 2928757 = 274571) (by norm_num)
theorem B3911813 : Blo 1156638 3911813 := bbase (se 4 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 3911813 = 733465) (by norm_num)
theorem B2928869 : Blo 1156638 2928869 := bbase (se 4 (by rfl) ⟨274581, by rfl⟩ : syracuseStep 2928869 = 549163) (by norm_num)
theorem B1323289 : Blo 1156638 1323289 := bbase (se 2 (by rfl) ⟨496233, by rfl⟩ : syracuseStep 1323289 = 992467) (by norm_num)
theorem B2470285 : Blo 1156638 2470285 := bbase (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) (by norm_num)
theorem B2929061 : Blo 1156638 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B1651117 : Blo 1156638 1651117 := bbase (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) (by norm_num)
theorem B7516597 : Blo 1156638 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B3912245 : Blo 1156638 3912245 := bbase (se 5 (by rfl) ⟨183386, by rfl⟩ : syracuseStep 3912245 = 366773) (by norm_num)
theorem B2929405 : Blo 1156638 2929405 := bbase (se 3 (by rfl) ⟨549263, by rfl⟩ : syracuseStep 2929405 = 1098527) (by norm_num)
theorem B2929517 : Blo 1156638 2929517 := bbase (se 3 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 2929517 = 1098569) (by norm_num)
theorem B3912677 : Blo 1156638 3912677 := bbase (se 4 (by rfl) ⟨366813, by rfl⟩ : syracuseStep 3912677 = 733627) (by norm_num)
theorem B1651709 : Blo 1156638 1651709 := bbase (se 3 (by rfl) ⟨309695, by rfl⟩ : syracuseStep 1651709 = 619391) (by norm_num)
theorem B2929709 : Blo 1156638 2929709 := bbase (se 3 (by rfl) ⟨549320, by rfl⟩ : syracuseStep 2929709 = 1098641) (by norm_num)
theorem B1651789 : Blo 1156638 1651789 := bbase (se 3 (by rfl) ⟨309710, by rfl⟩ : syracuseStep 1651789 = 619421) (by norm_num)
theorem B4174949 : Blo 1156638 4174949 := bbase (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) (by norm_num)
theorem B1389685 : Blo 1156638 1389685 := bbase (se 5 (by rfl) ⟨65141, by rfl⟩ : syracuseStep 1389685 = 130283) (by norm_num)
theorem B1651909 : Blo 1156638 1651909 := bbase (se 4 (by rfl) ⟨154866, by rfl⟩ : syracuseStep 1651909 = 309733) (by norm_num)
theorem B1652005 : Blo 1156638 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B2930053 : Blo 1156638 2930053 := bbase (se 4 (by rfl) ⟨274692, by rfl⟩ : syracuseStep 2930053 = 549385) (by norm_num)
theorem B3913109 : Blo 1156638 3913109 := bbase (se 6 (by rfl) ⟨91713, by rfl⟩ : syracuseStep 3913109 = 183427) (by norm_num)
theorem B1389997 : Blo 1156638 1389997 := bbase (se 3 (by rfl) ⟨260624, by rfl⟩ : syracuseStep 1389997 = 521249) (by norm_num)
theorem B2471413 : Blo 1156638 2471413 := bbase (se 5 (by rfl) ⟨115847, by rfl⟩ : syracuseStep 2471413 = 231695) (by norm_num)
theorem B2930165 : Blo 1156638 2930165 := bbase (se 5 (by rfl) ⟨137351, by rfl⟩ : syracuseStep 2930165 = 274703) (by norm_num)
theorem B4404725 : Blo 1156638 4404725 := bbase (se 5 (by rfl) ⟨206471, by rfl⟩ : syracuseStep 4404725 = 412943) (by norm_num)
theorem B2602493 : Blo 1156638 2602493 := bbase (se 3 (by rfl) ⟨487967, by rfl⟩ : syracuseStep 2602493 = 975935) (by norm_num)
theorem B2602565 : Blo 1156638 2602565 := bbase (se 4 (by rfl) ⟨243990, by rfl⟩ : syracuseStep 2602565 = 487981) (by norm_num)
theorem B2602637 : Blo 1156638 2602637 := bbase (se 3 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 2602637 = 975989) (by norm_num)
theorem B1586837 : Blo 1156638 1586837 := bbase (se 6 (by rfl) ⟨37191, by rfl⟩ : syracuseStep 1586837 = 74383) (by norm_num)
theorem B2930357 : Blo 1156638 2930357 := bbase (se 5 (by rfl) ⟨137360, by rfl⟩ : syracuseStep 2930357 = 274721) (by norm_num)
theorem B2602709 : Blo 1156638 2602709 := bbase (se 7 (by rfl) ⟨30500, by rfl⟩ : syracuseStep 2602709 = 61001) (by norm_num)
theorem B2143997 : Blo 1156638 2143997 := bbase (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) (by norm_num)
theorem B4405013 : Blo 1156638 4405013 := bbase (se 6 (by rfl) ⟨103242, by rfl⟩ : syracuseStep 4405013 = 206485) (by norm_num)
theorem B1652501 : Blo 1156638 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B2602781 : Blo 1156638 2602781 := bbase (se 3 (by rfl) ⟨488021, by rfl⟩ : syracuseStep 2602781 = 976043) (by norm_num)
theorem B3913541 : Blo 1156638 3913541 := bbase (se 4 (by rfl) ⟨366894, by rfl⟩ : syracuseStep 3913541 = 733789) (by norm_num)
theorem B2602853 : Blo 1156638 2602853 := bbase (se 4 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 2602853 = 488035) (by norm_num)
theorem B2471789 : Blo 1156638 2471789 := bbase (se 3 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 2471789 = 926921) (by norm_num)
theorem B2602925 : Blo 1156638 2602925 := bbase (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) (by norm_num)
theorem B2602997 : Blo 1156638 2602997 := bbase (se 5 (by rfl) ⟨122015, by rfl⟩ : syracuseStep 2602997 = 244031) (by norm_num)
theorem B2930701 : Blo 1156638 2930701 := bbase (se 3 (by rfl) ⟨549506, by rfl⟩ : syracuseStep 2930701 = 1099013) (by norm_num)
theorem B2603069 : Blo 1156638 2603069 := bbase (se 3 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 2603069 = 976151) (by norm_num)
theorem B2930813 : Blo 1156638 2930813 := bbase (se 3 (by rfl) ⟨549527, by rfl⟩ : syracuseStep 2930813 = 1099055) (by norm_num)
theorem B2603141 : Blo 1156638 2603141 := bbase (se 4 (by rfl) ⟨244044, by rfl⟩ : syracuseStep 2603141 = 488089) (by norm_num)
theorem B2603213 : Blo 1156638 2603213 := bbase (se 3 (by rfl) ⟨488102, by rfl⟩ : syracuseStep 2603213 = 976205) (by norm_num)
theorem B3913973 : Blo 1156638 3913973 := bbase (se 5 (by rfl) ⟨183467, by rfl⟩ : syracuseStep 3913973 = 366935) (by norm_num)
theorem B2603285 : Blo 1156638 2603285 := bbase (se 6 (by rfl) ⟨61014, by rfl⟩ : syracuseStep 2603285 = 122029) (by norm_num)
theorem B2931005 : Blo 1156638 2931005 := bbase (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) (by norm_num)
theorem B2603357 : Blo 1156638 2603357 := bbase (se 3 (by rfl) ⟨488129, by rfl⟩ : syracuseStep 2603357 = 976259) (by norm_num)
theorem B2603429 : Blo 1156638 2603429 := bbase (se 4 (by rfl) ⟨244071, by rfl⟩ : syracuseStep 2603429 = 488143) (by norm_num)
theorem B2603501 : Blo 1156638 2603501 := bbase (se 3 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 2603501 = 976313) (by norm_num)
theorem B2603573 : Blo 1156638 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B2603645 : Blo 1156638 2603645 := bbase (se 3 (by rfl) ⟨488183, by rfl⟩ : syracuseStep 2603645 = 976367) (by norm_num)
theorem B2931349 : Blo 1156638 2931349 := bbase (se 6 (by rfl) ⟨68703, by rfl⟩ : syracuseStep 2931349 = 137407) (by norm_num)
theorem B3914405 : Blo 1156638 3914405 := bbase (se 4 (by rfl) ⟨366975, by rfl⟩ : syracuseStep 3914405 = 733951) (by norm_num)
theorem B2603717 : Blo 1156638 2603717 := bbase (se 4 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 2603717 = 488197) (by norm_num)
theorem B2931461 : Blo 1156638 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B2603789 : Blo 1156638 2603789 := bbase (se 3 (by rfl) ⟨488210, by rfl⟩ : syracuseStep 2603789 = 976421) (by norm_num)
theorem B2603861 : Blo 1156638 2603861 := bbase (se 9 (by rfl) ⟨7628, by rfl⟩ : syracuseStep 2603861 = 15257) (by norm_num)
theorem B1391477 : Blo 1156638 1391477 := bbase (se 5 (by rfl) ⟨65225, by rfl⟩ : syracuseStep 1391477 = 130451) (by norm_num)
theorem B3718037 : Blo 1156638 3718037 := bbase (se 6 (by rfl) ⟨87141, by rfl⟩ : syracuseStep 3718037 = 174283) (by norm_num)
theorem B2603933 : Blo 1156638 2603933 := bbase (se 3 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 2603933 = 976475) (by norm_num)
theorem B4406197 : Blo 1156638 4406197 := bbase (se 5 (by rfl) ⟨206540, by rfl⟩ : syracuseStep 4406197 = 413081) (by norm_num)
theorem B2931653 : Blo 1156638 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B1391573 : Blo 1156638 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B2604005 : Blo 1156638 2604005 := bbase (se 4 (by rfl) ⟨244125, by rfl⟩ : syracuseStep 2604005 = 488251) (by norm_num)
theorem B1391593 : Blo 1156638 1391593 := bbase (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) (by norm_num)
theorem B2604077 : Blo 1156638 2604077 := bbase (se 3 (by rfl) ⟨488264, by rfl⟩ : syracuseStep 2604077 = 976529) (by norm_num)
theorem B3914837 : Blo 1156638 3914837 := bbase (se 8 (by rfl) ⟨22938, by rfl⟩ : syracuseStep 3914837 = 45877) (by norm_num)
theorem B2604149 : Blo 1156638 2604149 := bbase (se 5 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 2604149 = 244139) (by norm_num)
theorem B1391737 : Blo 1156638 1391737 := bbase (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) (by norm_num)
theorem B2604221 : Blo 1156638 2604221 := bbase (se 3 (by rfl) ⟨488291, by rfl⟩ : syracuseStep 2604221 = 976583) (by norm_num)
theorem B4406501 : Blo 1156638 4406501 := bbase (se 4 (by rfl) ⟨413109, by rfl⟩ : syracuseStep 4406501 = 826219) (by norm_num)
theorem B2604293 : Blo 1156638 2604293 := bbase (se 4 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 2604293 = 488305) (by norm_num)
theorem B2931997 : Blo 1156638 2931997 := bbase (se 3 (by rfl) ⟨549749, by rfl⟩ : syracuseStep 2931997 = 1099499) (by norm_num)
theorem B2604365 : Blo 1156638 2604365 := bbase (se 3 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 2604365 = 976637) (by norm_num)
theorem B11124053 : Blo 1156638 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B1981829 : Blo 1156638 1981829 := bbase (se 4 (by rfl) ⟨185796, by rfl⟩ : syracuseStep 1981829 = 371593) (by norm_num)
theorem B2932109 : Blo 1156638 2932109 := bbase (se 3 (by rfl) ⟨549770, by rfl⟩ : syracuseStep 2932109 = 1099541) (by norm_num)
theorem B2604437 : Blo 1156638 2604437 := bbase (se 6 (by rfl) ⟨61041, by rfl⟩ : syracuseStep 2604437 = 122083) (by norm_num)
theorem B2473429 : Blo 1156638 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B2604509 : Blo 1156638 2604509 := bbase (se 3 (by rfl) ⟨488345, by rfl⟩ : syracuseStep 2604509 = 976691) (by norm_num)
theorem B3915269 : Blo 1156638 3915269 := bbase (se 4 (by rfl) ⟨367056, by rfl⟩ : syracuseStep 3915269 = 734113) (by norm_num)
theorem B2604581 : Blo 1156638 2604581 := bbase (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) (by norm_num)
theorem B2932301 : Blo 1156638 2932301 := bbase (se 3 (by rfl) ⟨549806, by rfl⟩ : syracuseStep 2932301 = 1099613) (by norm_num)
theorem B2604653 : Blo 1156638 2604653 := bbase (se 3 (by rfl) ⟨488372, by rfl⟩ : syracuseStep 2604653 = 976745) (by norm_num)
theorem B20332181 : Blo 1156638 20332181 := bbase (se 6 (by rfl) ⟨476535, by rfl⟩ : syracuseStep 20332181 = 953071) (by norm_num)
theorem B2604725 : Blo 1156638 2604725 := bbase (se 5 (by rfl) ⟨122096, by rfl⟩ : syracuseStep 2604725 = 244193) (by norm_num)
theorem B2604797 : Blo 1156638 2604797 := bbase (se 3 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 2604797 = 976799) (by norm_num)
theorem B2604869 : Blo 1156638 2604869 := bbase (se 4 (by rfl) ⟨244206, by rfl⟩ : syracuseStep 2604869 = 488413) (by norm_num)
theorem B2604941 : Blo 1156638 2604941 := bbase (se 3 (by rfl) ⟨488426, by rfl⟩ : syracuseStep 2604941 = 976853) (by norm_num)
theorem B2932645 : Blo 1156638 2932645 := bbase (se 4 (by rfl) ⟨274935, by rfl⟩ : syracuseStep 2932645 = 549871) (by norm_num)
theorem B3915701 : Blo 1156638 3915701 := bbase (se 5 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 3915701 = 367097) (by norm_num)
theorem B2605013 : Blo 1156638 2605013 := bbase (se 7 (by rfl) ⟨30527, by rfl⟩ : syracuseStep 2605013 = 61055) (by norm_num)
theorem B2932757 : Blo 1156638 2932757 := bbase (se 6 (by rfl) ⟨68736, by rfl⟩ : syracuseStep 2932757 = 137473) (by norm_num)
theorem B2605085 : Blo 1156638 2605085 := bbase (se 3 (by rfl) ⟨488453, by rfl⟩ : syracuseStep 2605085 = 976907) (by norm_num)
theorem B2605157 : Blo 1156638 2605157 := bbase (se 4 (by rfl) ⟨244233, by rfl⟩ : syracuseStep 2605157 = 488467) (by norm_num)
theorem B2605229 : Blo 1156638 2605229 := bbase (se 3 (by rfl) ⟨488480, by rfl⟩ : syracuseStep 2605229 = 976961) (by norm_num)
theorem B2932949 : Blo 1156638 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B2605301 : Blo 1156638 2605301 := bbase (se 5 (by rfl) ⟨122123, by rfl⟩ : syracuseStep 2605301 = 244247) (by norm_num)
theorem B2605373 : Blo 1156638 2605373 := bbase (se 3 (by rfl) ⟨488507, by rfl⟩ : syracuseStep 2605373 = 977015) (by norm_num)
theorem B2474317 : Blo 1156638 2474317 := bbase (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) (by norm_num)
theorem B3916133 : Blo 1156638 3916133 := bbase (se 4 (by rfl) ⟨367137, by rfl⟩ : syracuseStep 3916133 = 734275) (by norm_num)
theorem B2605445 : Blo 1156638 2605445 := bbase (se 4 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 2605445 = 488521) (by norm_num)
theorem B1982909 : Blo 1156638 1982909 := bbase (se 3 (by rfl) ⟨371795, by rfl⟩ : syracuseStep 1982909 = 743591) (by norm_num)
theorem B2605517 : Blo 1156638 2605517 := bbase (se 3 (by rfl) ⟨488534, by rfl⟩ : syracuseStep 2605517 = 977069) (by norm_num)
theorem B2507213 : Blo 1156638 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B2605589 : Blo 1156638 2605589 := bbase (se 6 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 2605589 = 122137) (by norm_num)
theorem B2933293 : Blo 1156638 2933293 := bbase (se 3 (by rfl) ⟨549992, by rfl⟩ : syracuseStep 2933293 = 1099985) (by norm_num)
theorem B2605661 : Blo 1156638 2605661 := bbase (se 3 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 2605661 = 977123) (by norm_num)
theorem B2933405 : Blo 1156638 2933405 := bbase (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) (by norm_num)
theorem B2605733 : Blo 1156638 2605733 := bbase (se 4 (by rfl) ⟨244287, by rfl⟩ : syracuseStep 2605733 = 488575) (by norm_num)
theorem B2605805 : Blo 1156638 2605805 := bbase (se 3 (by rfl) ⟨488588, by rfl⟩ : syracuseStep 2605805 = 977177) (by norm_num)
theorem B3293941 : Blo 1156638 3293941 := bbase (se 5 (by rfl) ⟨154403, by rfl⟩ : syracuseStep 3293941 = 308807) (by norm_num)
theorem B3916565 : Blo 1156638 3916565 := bbase (se 6 (by rfl) ⟨91794, by rfl⟩ : syracuseStep 3916565 = 183589) (by norm_num)
theorem B2605877 : Blo 1156638 2605877 := bbase (se 5 (by rfl) ⟨122150, by rfl⟩ : syracuseStep 2605877 = 244301) (by norm_num)
theorem B8799029 : Blo 1156638 8799029 := bbase (se 5 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 8799029 = 824909) (by norm_num)
theorem B2474813 : Blo 1156638 2474813 := bbase (se 3 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 2474813 = 928055) (by norm_num)
theorem B20071253 : Blo 1156638 20071253 := bbase (se 9 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 20071253 = 117605) (by norm_num)
theorem B2933597 : Blo 1156638 2933597 := bbase (se 3 (by rfl) ⟨550049, by rfl⟩ : syracuseStep 2933597 = 1100099) (by norm_num)
theorem B1393529 : Blo 1156638 1393529 := bbase (se 2 (by rfl) ⟨522573, by rfl⟩ : syracuseStep 1393529 = 1045147) (by norm_num)
theorem B2605949 : Blo 1156638 2605949 := bbase (se 3 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 2605949 = 977231) (by norm_num)
theorem B3294101 : Blo 1156638 3294101 := bbase (se 6 (by rfl) ⟨77205, by rfl⟩ : syracuseStep 3294101 = 154411) (by norm_num)
theorem B2606021 : Blo 1156638 2606021 := bbase (se 4 (by rfl) ⟨244314, by rfl⟩ : syracuseStep 2606021 = 488629) (by norm_num)
theorem B2606093 : Blo 1156638 2606093 := bbase (se 3 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 2606093 = 977285) (by norm_num)
theorem B2606165 : Blo 1156638 2606165 := bbase (se 8 (by rfl) ⟨15270, by rfl⟩ : syracuseStep 2606165 = 30541) (by norm_num)
theorem B3294341 : Blo 1156638 3294341 := bbase (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) (by norm_num)
theorem B1787029 : Blo 1156638 1787029 := bbase (se 6 (by rfl) ⟨41883, by rfl⟩ : syracuseStep 1787029 = 83767) (by norm_num)
theorem B2606237 : Blo 1156638 2606237 := bbase (se 3 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 2606237 = 977339) (by norm_num)
theorem B7423157 : Blo 1156638 7423157 := bbase (se 5 (by rfl) ⟨347960, by rfl⟩ : syracuseStep 7423157 = 695921) (by norm_num)
theorem B2933941 : Blo 1156638 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1393861 : Blo 1156638 1393861 := bbase (se 4 (by rfl) ⟨130674, by rfl⟩ : syracuseStep 1393861 = 261349) (by norm_num)
theorem B3916997 : Blo 1156638 3916997 := bbase (se 4 (by rfl) ⟨367218, by rfl⟩ : syracuseStep 3916997 = 734437) (by norm_num)
theorem B3130597 : Blo 1156638 3130597 := bbase (se 4 (by rfl) ⟨293493, by rfl⟩ : syracuseStep 3130597 = 586987) (by norm_num)
theorem B2606309 : Blo 1156638 2606309 := bbase (se 4 (by rfl) ⟨244341, by rfl⟩ : syracuseStep 2606309 = 488683) (by norm_num)
theorem B2934053 : Blo 1156638 2934053 := bbase (se 4 (by rfl) ⟨275067, by rfl⟩ : syracuseStep 2934053 = 550135) (by norm_num)
theorem B2606381 : Blo 1156638 2606381 := bbase (se 3 (by rfl) ⟨488696, by rfl⟩ : syracuseStep 2606381 = 977393) (by norm_num)
theorem B3294533 : Blo 1156638 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B56411477 : Blo 1156638 56411477 := bbase (se 12 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 56411477 = 41317) (by norm_num)
theorem B1394005 : Blo 1156638 1394005 := bbase (se 12 (by rfl) ⟨510, by rfl⟩ : syracuseStep 1394005 = 1021) (by norm_num)
theorem B2606453 : Blo 1156638 2606453 := bbase (se 5 (by rfl) ⟨122177, by rfl⟩ : syracuseStep 2606453 = 244355) (by norm_num)
theorem B2606525 : Blo 1156638 2606525 := bbase (se 3 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 2606525 = 977447) (by norm_num)
theorem B2934245 : Blo 1156638 2934245 := bbase (se 4 (by rfl) ⟨275085, by rfl⟩ : syracuseStep 2934245 = 550171) (by norm_num)
theorem B1983989 : Blo 1156638 1983989 := bbase (se 5 (by rfl) ⟨92999, by rfl⟩ : syracuseStep 1983989 = 185999) (by norm_num)
theorem B2606597 : Blo 1156638 2606597 := bbase (se 4 (by rfl) ⟨244368, by rfl⟩ : syracuseStep 2606597 = 488737) (by norm_num)
theorem B2606669 : Blo 1156638 2606669 := bbase (se 3 (by rfl) ⟨488750, by rfl⟩ : syracuseStep 2606669 = 977501) (by norm_num)
theorem B2606741 : Blo 1156638 2606741 := bbase (se 6 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 2606741 = 122191) (by norm_num)
theorem B2475677 : Blo 1156638 2475677 := bbase (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) (by norm_num)
theorem B4703957 : Blo 1156638 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B2606813 : Blo 1156638 2606813 := bbase (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) (by norm_num)
theorem B5949173 : Blo 1156638 5949173 := bbase (se 5 (by rfl) ⟨278867, by rfl⟩ : syracuseStep 5949173 = 557735) (by norm_num)
theorem B1853189 : Blo 1156638 1853189 := bbase (se 4 (by rfl) ⟨173736, by rfl⟩ : syracuseStep 1853189 = 347473) (by norm_num)
theorem B1853221 : Blo 1156638 1853221 := bbase (se 4 (by rfl) ⟨173739, by rfl⟩ : syracuseStep 1853221 = 347479) (by norm_num)
theorem B2606885 : Blo 1156638 2606885 := bbase (se 4 (by rfl) ⟨244395, by rfl⟩ : syracuseStep 2606885 = 488791) (by norm_num)
theorem B2475821 : Blo 1156638 2475821 := bbase (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) (by norm_num)
theorem B2934589 : Blo 1156638 2934589 := bbase (se 3 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 2934589 = 1100471) (by norm_num)
theorem B2606957 : Blo 1156638 2606957 := bbase (se 3 (by rfl) ⟨488804, by rfl⟩ : syracuseStep 2606957 = 977609) (by norm_num)
theorem B2934701 : Blo 1156638 2934701 := bbase (se 3 (by rfl) ⟨550256, by rfl⟩ : syracuseStep 2934701 = 1100513) (by norm_num)
theorem B2607029 : Blo 1156638 2607029 := bbase (se 5 (by rfl) ⟨122204, by rfl⟩ : syracuseStep 2607029 = 244409) (by norm_num)
theorem B2607101 : Blo 1156638 2607101 := bbase (se 3 (by rfl) ⟨488831, by rfl⟩ : syracuseStep 2607101 = 977663) (by norm_num)
theorem B2607173 : Blo 1156638 2607173 := bbase (se 4 (by rfl) ⟨244422, by rfl⟩ : syracuseStep 2607173 = 488845) (by norm_num)
theorem B2934893 : Blo 1156638 2934893 := bbase (se 3 (by rfl) ⟨550292, by rfl⟩ : syracuseStep 2934893 = 1100585) (by norm_num)
theorem B1951877 : Blo 1156638 1951877 := bbase (se 4 (by rfl) ⟨182988, by rfl⟩ : syracuseStep 1951877 = 365977) (by norm_num)
theorem B2607245 : Blo 1156638 2607245 := bbase (se 3 (by rfl) ⟨488858, by rfl⟩ : syracuseStep 2607245 = 977717) (by norm_num)
theorem B2607317 : Blo 1156638 2607317 := bbase (se 7 (by rfl) ⟨30554, by rfl⟩ : syracuseStep 2607317 = 61109) (by norm_num)
theorem B1952005 : Blo 1156638 1952005 := bbase (se 4 (by rfl) ⟨183000, by rfl⟩ : syracuseStep 1952005 = 366001) (by norm_num)
theorem B2607389 : Blo 1156638 2607389 := bbase (se 3 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 2607389 = 977771) (by norm_num)
theorem B3295525 : Blo 1156638 3295525 := bbase (se 4 (by rfl) ⟨308955, by rfl⟩ : syracuseStep 3295525 = 617911) (by norm_num)
theorem B1952093 : Blo 1156638 1952093 := bbase (se 3 (by rfl) ⟨366017, by rfl⟩ : syracuseStep 1952093 = 732035) (by norm_num)
theorem B2607461 : Blo 1156638 2607461 := bbase (se 4 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 2607461 = 488899) (by norm_num)
theorem B2607533 : Blo 1156638 2607533 := bbase (se 3 (by rfl) ⟨488912, by rfl⟩ : syracuseStep 2607533 = 977825) (by norm_num)
theorem B2935237 : Blo 1156638 2935237 := bbase (se 4 (by rfl) ⟨275178, by rfl⟩ : syracuseStep 2935237 = 550357) (by norm_num)
theorem B1952221 : Blo 1156638 1952221 := bbase (se 3 (by rfl) ⟨366041, by rfl⟩ : syracuseStep 1952221 = 732083) (by norm_num)
theorem B2607605 : Blo 1156638 2607605 := bbase (se 5 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 2607605 = 244463) (by norm_num)
theorem B2476565 : Blo 1156638 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B6605333 : Blo 1156638 6605333 := bbase (se 6 (by rfl) ⟨154812, by rfl⟩ : syracuseStep 6605333 = 309625) (by norm_num)
theorem B1952309 : Blo 1156638 1952309 := bbase (se 5 (by rfl) ⟨91514, by rfl⟩ : syracuseStep 1952309 = 183029) (by norm_num)
theorem B2935349 : Blo 1156638 2935349 := bbase (se 5 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 2935349 = 275189) (by norm_num)
theorem B2607677 : Blo 1156638 2607677 := bbase (se 3 (by rfl) ⟨488939, by rfl⟩ : syracuseStep 2607677 = 977879) (by norm_num)
theorem B2607749 : Blo 1156638 2607749 := bbase (se 4 (by rfl) ⟨244476, by rfl⟩ : syracuseStep 2607749 = 488953) (by norm_num)
theorem B1952437 : Blo 1156638 1952437 := bbase (se 5 (by rfl) ⟨91520, by rfl⟩ : syracuseStep 1952437 = 183041) (by norm_num)
theorem B1854149 : Blo 1156638 1854149 := bbase (se 4 (by rfl) ⟨173826, by rfl⟩ : syracuseStep 1854149 = 347653) (by norm_num)
theorem B2607821 : Blo 1156638 2607821 := bbase (se 3 (by rfl) ⟨488966, by rfl⟩ : syracuseStep 2607821 = 977933) (by norm_num)
theorem B32197333 : Blo 1156638 32197333 := bbase (se 7 (by rfl) ⟨377312, by rfl⟩ : syracuseStep 32197333 = 754625) (by norm_num)
theorem B2935541 : Blo 1156638 2935541 := bbase (se 5 (by rfl) ⟨137603, by rfl⟩ : syracuseStep 2935541 = 275207) (by norm_num)
theorem B1952525 : Blo 1156638 1952525 := bbase (se 3 (by rfl) ⟨366098, by rfl⟩ : syracuseStep 1952525 = 732197) (by norm_num)
theorem B2607893 : Blo 1156638 2607893 := bbase (se 6 (by rfl) ⟨61122, by rfl⟩ : syracuseStep 2607893 = 122245) (by norm_num)
theorem B2607965 : Blo 1156638 2607965 := bbase (se 3 (by rfl) ⟨488993, by rfl⟩ : syracuseStep 2607965 = 977987) (by norm_num)
theorem B2640757 : Blo 1156638 2640757 := bbase (se 5 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 2640757 = 247571) (by norm_num)
theorem B1952653 : Blo 1156638 1952653 := bbase (se 3 (by rfl) ⟨366122, by rfl⟩ : syracuseStep 1952653 = 732245) (by norm_num)
theorem B2608037 : Blo 1156638 2608037 := bbase (se 4 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 2608037 = 489007) (by norm_num)
theorem B4705237 : Blo 1156638 4705237 := bbase (se 7 (by rfl) ⟨55139, by rfl⟩ : syracuseStep 4705237 = 110279) (by norm_num)
theorem B1952741 : Blo 1156638 1952741 := bbase (se 4 (by rfl) ⟨183069, by rfl⟩ : syracuseStep 1952741 = 366139) (by norm_num)
theorem B2608109 : Blo 1156638 2608109 := bbase (se 3 (by rfl) ⟨489020, by rfl⟩ : syracuseStep 2608109 = 978041) (by norm_num)
theorem B2608181 : Blo 1156638 2608181 := bbase (se 5 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 2608181 = 244517) (by norm_num)
theorem B2935885 : Blo 1156638 2935885 := bbase (se 3 (by rfl) ⟨550478, by rfl⟩ : syracuseStep 2935885 = 1100957) (by norm_num)
theorem B1952869 : Blo 1156638 1952869 := bbase (se 4 (by rfl) ⟨183081, by rfl⟩ : syracuseStep 1952869 = 366163) (by norm_num)
theorem B3132533 : Blo 1156638 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B2608253 : Blo 1156638 2608253 := bbase (se 3 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 2608253 = 978095) (by norm_num)
theorem B1952957 : Blo 1156638 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B2935997 : Blo 1156638 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B2608325 : Blo 1156638 2608325 := bbase (se 4 (by rfl) ⟨244530, by rfl⟩ : syracuseStep 2608325 = 489061) (by norm_num)
theorem B2477317 : Blo 1156638 2477317 := bbase (se 4 (by rfl) ⟨232248, by rfl⟩ : syracuseStep 2477317 = 464497) (by norm_num)
theorem B2608397 : Blo 1156638 2608397 := bbase (se 3 (by rfl) ⟨489074, by rfl⟩ : syracuseStep 2608397 = 978149) (by norm_num)
theorem B2346301 : Blo 1156638 2346301 := bbase (se 3 (by rfl) ⟨439931, by rfl⟩ : syracuseStep 2346301 = 879863) (by norm_num)
theorem B1953085 : Blo 1156638 1953085 := bbase (se 3 (by rfl) ⟨366203, by rfl⟩ : syracuseStep 1953085 = 732407) (by norm_num)
theorem B2608469 : Blo 1156638 2608469 := bbase (se 11 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 2608469 = 3821) (by norm_num)
theorem B1854829 : Blo 1156638 1854829 := bbase (se 3 (by rfl) ⟨347780, by rfl⟩ : syracuseStep 1854829 = 695561) (by norm_num)
theorem B3296629 : Blo 1156638 3296629 := bbase (se 5 (by rfl) ⟨154529, by rfl⟩ : syracuseStep 3296629 = 309059) (by norm_num)
theorem B2936189 : Blo 1156638 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B1953173 : Blo 1156638 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B2477461 : Blo 1156638 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B2608541 : Blo 1156638 2608541 := bbase (se 3 (by rfl) ⟨489101, by rfl⟩ : syracuseStep 2608541 = 978203) (by norm_num)
theorem B1854893 : Blo 1156638 1854893 := bbase (se 3 (by rfl) ⟨347792, by rfl⟩ : syracuseStep 1854893 = 695585) (by norm_num)
theorem B2608613 : Blo 1156638 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B2379269 : Blo 1156638 2379269 := bbase (se 4 (by rfl) ⟨223056, by rfl⟩ : syracuseStep 2379269 = 446113) (by norm_num)
theorem B1953301 : Blo 1156638 1953301 := bbase (se 6 (by rfl) ⟨45780, by rfl⟩ : syracuseStep 1953301 = 91561) (by norm_num)
theorem B2608685 : Blo 1156638 2608685 := bbase (se 3 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 2608685 = 978257) (by norm_num)
theorem B2084413 : Blo 1156638 2084413 := bbase (se 3 (by rfl) ⟨390827, by rfl⟩ : syracuseStep 2084413 = 781655) (by norm_num)
theorem B1953389 : Blo 1156638 1953389 := bbase (se 3 (by rfl) ⟨366260, by rfl⟩ : syracuseStep 1953389 = 732521) (by norm_num)
theorem B2608757 : Blo 1156638 2608757 := bbase (se 5 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 2608757 = 244571) (by norm_num)
theorem B2641589 : Blo 1156638 2641589 := bbase (se 5 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 2641589 = 247649) (by norm_num)
theorem B2608829 : Blo 1156638 2608829 := bbase (se 3 (by rfl) ⟨489155, by rfl⟩ : syracuseStep 2608829 = 978311) (by norm_num)
theorem B2936533 : Blo 1156638 2936533 := bbase (se 7 (by rfl) ⟨34412, by rfl⟩ : syracuseStep 2936533 = 68825) (by norm_num)
theorem B1953517 : Blo 1156638 1953517 := bbase (se 3 (by rfl) ⟨366284, by rfl⟩ : syracuseStep 1953517 = 732569) (by norm_num)
theorem B2608901 : Blo 1156638 2608901 := bbase (se 4 (by rfl) ⟨244584, by rfl⟩ : syracuseStep 2608901 = 489169) (by norm_num)
theorem B2084621 : Blo 1156638 2084621 := bbase (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) (by norm_num)
theorem B2477837 : Blo 1156638 2477837 := bbase (se 3 (by rfl) ⟨464594, by rfl⟩ : syracuseStep 2477837 = 929189) (by norm_num)
theorem B4181813 : Blo 1156638 4181813 := bbase (se 5 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 4181813 = 392045) (by norm_num)
theorem B1953605 : Blo 1156638 1953605 := bbase (se 4 (by rfl) ⟨183150, by rfl⟩ : syracuseStep 1953605 = 366301) (by norm_num)
theorem B2936645 : Blo 1156638 2936645 := bbase (se 4 (by rfl) ⟨275310, by rfl⟩ : syracuseStep 2936645 = 550621) (by norm_num)
theorem B2608973 : Blo 1156638 2608973 := bbase (se 3 (by rfl) ⟨489182, by rfl⟩ : syracuseStep 2608973 = 978365) (by norm_num)
theorem B2609045 : Blo 1156638 2609045 := bbase (se 6 (by rfl) ⟨61149, by rfl⟩ : syracuseStep 2609045 = 122299) (by norm_num)
theorem B1953733 : Blo 1156638 1953733 := bbase (se 4 (by rfl) ⟨183162, by rfl⟩ : syracuseStep 1953733 = 366325) (by norm_num)
theorem B2609117 : Blo 1156638 2609117 := bbase (se 3 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 2609117 = 978419) (by norm_num)
theorem B2936837 : Blo 1156638 2936837 := bbase (se 4 (by rfl) ⟨275328, by rfl⟩ : syracuseStep 2936837 = 550657) (by norm_num)
theorem B1953821 : Blo 1156638 1953821 := bbase (se 3 (by rfl) ⟨366341, by rfl⟩ : syracuseStep 1953821 = 732683) (by norm_num)
theorem B2609189 : Blo 1156638 2609189 := bbase (se 4 (by rfl) ⟨244611, by rfl⟩ : syracuseStep 2609189 = 489223) (by norm_num)
theorem B2510909 : Blo 1156638 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B4182101 : Blo 1156638 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B2609261 : Blo 1156638 2609261 := bbase (se 3 (by rfl) ⟨489236, by rfl⟩ : syracuseStep 2609261 = 978473) (by norm_num)
theorem B2478205 : Blo 1156638 2478205 := bbase (se 3 (by rfl) ⟨464663, by rfl⟩ : syracuseStep 2478205 = 929327) (by norm_num)
theorem B1953949 : Blo 1156638 1953949 := bbase (se 3 (by rfl) ⟨366365, by rfl⟩ : syracuseStep 1953949 = 732731) (by norm_num)
theorem B2609333 : Blo 1156638 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B1954037 : Blo 1156638 1954037 := bbase (se 5 (by rfl) ⟨91595, by rfl⟩ : syracuseStep 1954037 = 183191) (by norm_num)
theorem B2609405 : Blo 1156638 2609405 := bbase (se 3 (by rfl) ⟨489263, by rfl⟩ : syracuseStep 2609405 = 978527) (by norm_num)
theorem B2609477 : Blo 1156638 2609477 := bbase (se 4 (by rfl) ⟨244638, by rfl⟩ : syracuseStep 2609477 = 489277) (by norm_num)
theorem B2937181 : Blo 1156638 2937181 := bbase (se 3 (by rfl) ⟨550721, by rfl⟩ : syracuseStep 2937181 = 1101443) (by norm_num)
theorem B1954165 : Blo 1156638 1954165 := bbase (se 5 (by rfl) ⟨91601, by rfl⟩ : syracuseStep 1954165 = 183203) (by norm_num)
theorem B2609549 : Blo 1156638 2609549 := bbase (se 3 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 2609549 = 978581) (by norm_num)
theorem B2347429 : Blo 1156638 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B1954253 : Blo 1156638 1954253 := bbase (se 3 (by rfl) ⟨366422, by rfl⟩ : syracuseStep 1954253 = 732845) (by norm_num)
theorem B2937293 : Blo 1156638 2937293 := bbase (se 3 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 2937293 = 1101485) (by norm_num)
theorem B2609621 : Blo 1156638 2609621 := bbase (se 7 (by rfl) ⟨30581, by rfl⟩ : syracuseStep 2609621 = 61163) (by norm_num)
theorem B2609693 : Blo 1156638 2609693 := bbase (se 3 (by rfl) ⟨489317, by rfl⟩ : syracuseStep 2609693 = 978635) (by norm_num)
theorem B1954381 : Blo 1156638 1954381 := bbase (se 3 (by rfl) ⟨366446, by rfl⟩ : syracuseStep 1954381 = 732893) (by norm_num)
theorem B2609765 : Blo 1156638 2609765 := bbase (se 4 (by rfl) ⟨244665, by rfl⟩ : syracuseStep 2609765 = 489331) (by norm_num)
theorem B2937485 : Blo 1156638 2937485 := bbase (se 3 (by rfl) ⟨550778, by rfl⟩ : syracuseStep 2937485 = 1101557) (by norm_num)
theorem B1954469 : Blo 1156638 1954469 := bbase (se 4 (by rfl) ⟨183231, by rfl⟩ : syracuseStep 1954469 = 366463) (by norm_num)
theorem B2609837 : Blo 1156638 2609837 := bbase (se 3 (by rfl) ⟨489344, by rfl⟩ : syracuseStep 2609837 = 978689) (by norm_num)
theorem B1856213 : Blo 1156638 1856213 := bbase (se 7 (by rfl) ⟨21752, by rfl⟩ : syracuseStep 1856213 = 43505) (by norm_num)
theorem B2577125 : Blo 1156638 2577125 := bbase (se 4 (by rfl) ⟨241605, by rfl⟩ : syracuseStep 2577125 = 483211) (by norm_num)
theorem B2609909 : Blo 1156638 2609909 := bbase (se 5 (by rfl) ⟨122339, by rfl⟩ : syracuseStep 2609909 = 244679) (by norm_num)
theorem B1954597 : Blo 1156638 1954597 := bbase (se 4 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 1954597 = 366487) (by norm_num)
theorem B5952293 : Blo 1156638 5952293 := bbase (se 4 (by rfl) ⟨558027, by rfl⟩ : syracuseStep 5952293 = 1116055) (by norm_num)
theorem B2609981 : Blo 1156638 2609981 := bbase (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) (by norm_num)
theorem B3298133 : Blo 1156638 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B1954685 : Blo 1156638 1954685 := bbase (se 3 (by rfl) ⟨366503, by rfl⟩ : syracuseStep 1954685 = 733007) (by norm_num)
theorem B2610053 : Blo 1156638 2610053 := bbase (se 4 (by rfl) ⟨244692, by rfl⟩ : syracuseStep 2610053 = 489385) (by norm_num)
theorem B2511749 : Blo 1156638 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B1856405 : Blo 1156638 1856405 := bbase (se 6 (by rfl) ⟨43509, by rfl⟩ : syracuseStep 1856405 = 87019) (by norm_num)
theorem B2610125 : Blo 1156638 2610125 := bbase (se 3 (by rfl) ⟨489398, by rfl⟩ : syracuseStep 2610125 = 978797) (by norm_num)
theorem B2937829 : Blo 1156638 2937829 := bbase (se 4 (by rfl) ⟨275421, by rfl⟩ : syracuseStep 2937829 = 550843) (by norm_num)
theorem B1954813 : Blo 1156638 1954813 := bbase (se 3 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 1954813 = 733055) (by norm_num)
theorem B9884693 : Blo 1156638 9884693 := bbase (se 6 (by rfl) ⟨231672, by rfl⟩ : syracuseStep 9884693 = 463345) (by norm_num)
theorem B1856533 : Blo 1156638 1856533 := bbase (se 6 (by rfl) ⟨43512, by rfl⟩ : syracuseStep 1856533 = 87025) (by norm_num)
theorem B2610197 : Blo 1156638 2610197 := bbase (se 6 (by rfl) ⟨61176, by rfl⟩ : syracuseStep 2610197 = 122353) (by norm_num)
theorem B1954901 : Blo 1156638 1954901 := bbase (se 8 (by rfl) ⟨11454, by rfl⟩ : syracuseStep 1954901 = 22909) (by norm_num)
theorem B2610269 : Blo 1156638 2610269 := bbase (se 3 (by rfl) ⟨489425, by rfl⟩ : syracuseStep 2610269 = 978851) (by norm_num)
theorem B3134629 : Blo 1156638 3134629 := bbase (se 4 (by rfl) ⟨293871, by rfl⟩ : syracuseStep 3134629 = 587743) (by norm_num)
theorem B2610341 : Blo 1156638 2610341 := bbase (se 4 (by rfl) ⟨244719, by rfl⟩ : syracuseStep 2610341 = 489439) (by norm_num)
theorem B1955029 : Blo 1156638 1955029 := bbase (se 7 (by rfl) ⟨22910, by rfl⟩ : syracuseStep 1955029 = 45821) (by norm_num)
theorem B2610413 : Blo 1156638 2610413 := bbase (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) (by norm_num)
theorem B1955117 : Blo 1156638 1955117 := bbase (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) (by norm_num)
theorem B2610485 : Blo 1156638 2610485 := bbase (se 5 (by rfl) ⟨122366, by rfl⟩ : syracuseStep 2610485 = 244733) (by norm_num)
theorem B2610557 : Blo 1156638 2610557 := bbase (se 3 (by rfl) ⟨489479, by rfl⟩ : syracuseStep 2610557 = 978959) (by norm_num)
theorem B1955245 : Blo 1156638 1955245 := bbase (se 3 (by rfl) ⟨366608, by rfl⟩ : syracuseStep 1955245 = 733217) (by norm_num)
theorem B2610629 : Blo 1156638 2610629 := bbase (se 4 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 2610629 = 489493) (by norm_num)
theorem B2086373 : Blo 1156638 2086373 := bbase (se 4 (by rfl) ⟨195597, by rfl⟩ : syracuseStep 2086373 = 391195) (by norm_num)
theorem B1955333 : Blo 1156638 1955333 := bbase (se 4 (by rfl) ⟨183312, by rfl⟩ : syracuseStep 1955333 = 366625) (by norm_num)
theorem B2610701 : Blo 1156638 2610701 := bbase (se 3 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 2610701 = 979013) (by norm_num)
theorem B2610773 : Blo 1156638 2610773 := bbase (se 8 (by rfl) ⟨15297, by rfl⟩ : syracuseStep 2610773 = 30595) (by norm_num)
theorem B1463933 : Blo 1156638 1463933 := bbase (se 3 (by rfl) ⟨274487, by rfl⟩ : syracuseStep 1463933 = 548975) (by norm_num)
theorem B1955461 : Blo 1156638 1955461 := bbase (se 4 (by rfl) ⟨183324, by rfl⟩ : syracuseStep 1955461 = 366649) (by norm_num)
theorem B1857173 : Blo 1156638 1857173 := bbase (se 6 (by rfl) ⟨43527, by rfl⟩ : syracuseStep 1857173 = 87055) (by norm_num)
theorem B2610845 : Blo 1156638 2610845 := bbase (se 3 (by rfl) ⟨489533, by rfl⟩ : syracuseStep 2610845 = 979067) (by norm_num)
theorem B1463989 : Blo 1156638 1463989 := bbase (se 5 (by rfl) ⟨68624, by rfl⟩ : syracuseStep 1463989 = 137249) (by norm_num)
theorem B1955549 : Blo 1156638 1955549 := bbase (se 3 (by rfl) ⟨366665, by rfl⟩ : syracuseStep 1955549 = 733331) (by norm_num)
theorem B2610917 : Blo 1156638 2610917 := bbase (se 4 (by rfl) ⟨244773, by rfl⟩ : syracuseStep 2610917 = 489547) (by norm_num)
theorem B1464085 : Blo 1156638 1464085 := bbase (se 6 (by rfl) ⟨34314, by rfl⟩ : syracuseStep 1464085 = 68629) (by norm_num)
theorem B2610989 : Blo 1156638 2610989 := bbase (se 3 (by rfl) ⟨489560, by rfl⟩ : syracuseStep 2610989 = 979121) (by norm_num)
theorem B1955677 : Blo 1156638 1955677 := bbase (se 3 (by rfl) ⟨366689, by rfl⟩ : syracuseStep 1955677 = 733379) (by norm_num)
theorem B2611061 : Blo 1156638 2611061 := bbase (se 5 (by rfl) ⟨122393, by rfl⟩ : syracuseStep 2611061 = 244787) (by norm_num)
theorem B3757957 : Blo 1156638 3757957 := bbase (se 4 (by rfl) ⟨352308, by rfl⟩ : syracuseStep 3757957 = 704617) (by norm_num)
theorem B2381717 : Blo 1156638 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B1955765 : Blo 1156638 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B2611133 : Blo 1156638 2611133 := bbase (se 3 (by rfl) ⟨489587, by rfl⟩ : syracuseStep 2611133 = 979175) (by norm_num)
theorem B1464257 : Blo 1156638 1464257 := bbase (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) (by norm_num)
theorem B2578405 : Blo 1156638 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B1464313 : Blo 1156638 1464313 := bbase (se 2 (by rfl) ⟨549117, by rfl⟩ : syracuseStep 1464313 = 1098235) (by norm_num)
theorem B1759229 : Blo 1156638 1759229 := bbase (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) (by norm_num)
theorem B2611205 : Blo 1156638 2611205 := bbase (se 4 (by rfl) ⟨244800, by rfl⟩ : syracuseStep 2611205 = 489601) (by norm_num)
theorem B1955893 : Blo 1156638 1955893 := bbase (se 5 (by rfl) ⟨91682, by rfl⟩ : syracuseStep 1955893 = 183365) (by norm_num)
theorem B2611277 : Blo 1156638 2611277 := bbase (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) (by norm_num)
theorem B1464409 : Blo 1156638 1464409 := bbase (se 2 (by rfl) ⟨549153, by rfl⟩ : syracuseStep 1464409 = 1098307) (by norm_num)
theorem B1857629 : Blo 1156638 1857629 := bbase (se 3 (by rfl) ⟨348305, by rfl⟩ : syracuseStep 1857629 = 696611) (by norm_num)
theorem B2349157 : Blo 1156638 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B1955981 : Blo 1156638 1955981 := bbase (se 3 (by rfl) ⟨366746, by rfl⟩ : syracuseStep 1955981 = 733493) (by norm_num)
theorem B2611349 : Blo 1156638 2611349 := bbase (se 6 (by rfl) ⟨61203, by rfl⟩ : syracuseStep 2611349 = 122407) (by norm_num)
theorem B2349253 : Blo 1156638 2349253 := bbase (se 4 (by rfl) ⟨220242, by rfl⟩ : syracuseStep 2349253 = 440485) (by norm_num)
theorem B15849685 : Blo 1156638 15849685 := bbase (se 7 (by rfl) ⟨185738, by rfl⟩ : syracuseStep 15849685 = 371477) (by norm_num)
theorem B2611421 : Blo 1156638 2611421 := bbase (se 3 (by rfl) ⟨489641, by rfl⟩ : syracuseStep 2611421 = 979283) (by norm_num)
theorem B1464581 : Blo 1156638 1464581 := bbase (se 4 (by rfl) ⟨137304, by rfl⟩ : syracuseStep 1464581 = 274609) (by norm_num)
theorem B1956109 : Blo 1156638 1956109 := bbase (se 3 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 1956109 = 733541) (by norm_num)
theorem B1464637 : Blo 1156638 1464637 := bbase (se 3 (by rfl) ⟨274619, by rfl⟩ : syracuseStep 1464637 = 549239) (by norm_num)
theorem B1857853 : Blo 1156638 1857853 := bbase (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) (by norm_num)
theorem B1956197 : Blo 1156638 1956197 := bbase (se 4 (by rfl) ⟨183393, by rfl⟩ : syracuseStep 1956197 = 366787) (by norm_num)
theorem B1857917 : Blo 1156638 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B3299717 : Blo 1156638 3299717 := bbase (se 4 (by rfl) ⟨309348, by rfl⟩ : syracuseStep 3299717 = 618697) (by norm_num)
theorem B2087317 : Blo 1156638 2087317 := bbase (se 6 (by rfl) ⟨48921, by rfl⟩ : syracuseStep 2087317 = 97843) (by norm_num)
theorem B1464733 : Blo 1156638 1464733 := bbase (se 3 (by rfl) ⟨274637, by rfl⟩ : syracuseStep 1464733 = 549275) (by norm_num)
theorem B5560757 : Blo 1156638 5560757 := bbase (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) (by norm_num)
theorem B8346037 : Blo 1156638 8346037 := bbase (se 5 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 8346037 = 782441) (by norm_num)
theorem B1956325 : Blo 1156638 1956325 := bbase (se 4 (by rfl) ⟨183405, by rfl⟩ : syracuseStep 1956325 = 366811) (by norm_num)
theorem B1858045 : Blo 1156638 1858045 := bbase (se 3 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 1858045 = 696767) (by norm_num)
theorem B1956413 : Blo 1156638 1956413 := bbase (se 3 (by rfl) ⟨366827, by rfl⟩ : syracuseStep 1956413 = 733655) (by norm_num)
theorem B5855813 : Blo 1156638 5855813 := bbase (se 4 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 5855813 = 1097965) (by norm_num)
theorem B1464905 : Blo 1156638 1464905 := bbase (se 2 (by rfl) ⟨549339, by rfl⟩ : syracuseStep 1464905 = 1098679) (by norm_num)
theorem B5560949 : Blo 1156638 5560949 := bbase (se 5 (by rfl) ⟨260669, by rfl⟩ : syracuseStep 5560949 = 521339) (by norm_num)
theorem B2382461 : Blo 1156638 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B1464961 : Blo 1156638 1464961 := bbase (se 2 (by rfl) ⟨549360, by rfl⟩ : syracuseStep 1464961 = 1098721) (by norm_num)
theorem B3136133 : Blo 1156638 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B1235621 : Blo 1156638 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B1759909 : Blo 1156638 1759909 := bbase (se 4 (by rfl) ⟨164991, by rfl⟩ : syracuseStep 1759909 = 329983) (by norm_num)
theorem B1956541 : Blo 1156638 1956541 := bbase (se 3 (by rfl) ⟨366851, by rfl⟩ : syracuseStep 1956541 = 733703) (by norm_num)
theorem B1465057 : Blo 1156638 1465057 := bbase (se 2 (by rfl) ⟨549396, by rfl⟩ : syracuseStep 1465057 = 1098793) (by norm_num)
theorem B1301233 : Blo 1156638 1301233 := bbase (se 2 (by rfl) ⟨487962, by rfl⟩ : syracuseStep 1301233 = 975925) (by norm_num)
theorem B1301269 : Blo 1156638 1301269 := bbase (se 6 (by rfl) ⟨30498, by rfl⟩ : syracuseStep 1301269 = 60997) (by norm_num)
theorem B1956629 : Blo 1156638 1956629 := bbase (se 6 (by rfl) ⟨45858, by rfl⟩ : syracuseStep 1956629 = 91717) (by norm_num)
theorem B1301305 : Blo 1156638 1301305 := bbase (se 2 (by rfl) ⟨487989, by rfl⟩ : syracuseStep 1301305 = 975979) (by norm_num)
theorem B1301341 : Blo 1156638 1301341 := bbase (se 3 (by rfl) ⟨244001, by rfl⟩ : syracuseStep 1301341 = 488003) (by norm_num)
theorem B1563509 : Blo 1156638 1563509 := bbase (se 5 (by rfl) ⟨73289, by rfl⟩ : syracuseStep 1563509 = 146579) (by norm_num)
theorem B1301377 : Blo 1156638 1301377 := bbase (se 2 (by rfl) ⟨488016, by rfl⟩ : syracuseStep 1301377 = 976033) (by norm_num)
theorem B1465229 : Blo 1156638 1465229 := bbase (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) (by norm_num)
theorem B1956757 : Blo 1156638 1956757 := bbase (se 6 (by rfl) ⟨45861, by rfl⟩ : syracuseStep 1956757 = 91723) (by norm_num)
theorem B1301413 : Blo 1156638 1301413 := bbase (se 4 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 1301413 = 244015) (by norm_num)
theorem B1465285 : Blo 1156638 1465285 := bbase (se 4 (by rfl) ⟨137370, by rfl⟩ : syracuseStep 1465285 = 274741) (by norm_num)
theorem B1301449 : Blo 1156638 1301449 := bbase (se 2 (by rfl) ⟨488043, by rfl⟩ : syracuseStep 1301449 = 976087) (by norm_num)
theorem B1301485 : Blo 1156638 1301485 := bbase (se 3 (by rfl) ⟨244028, by rfl⟩ : syracuseStep 1301485 = 488057) (by norm_num)
theorem B1956845 : Blo 1156638 1956845 := bbase (se 3 (by rfl) ⟨366908, by rfl⟩ : syracuseStep 1956845 = 733817) (by norm_num)
theorem B1301521 : Blo 1156638 1301521 := bbase (se 2 (by rfl) ⟨488070, by rfl⟩ : syracuseStep 1301521 = 976141) (by norm_num)
theorem B1465381 : Blo 1156638 1465381 := bbase (se 4 (by rfl) ⟨137379, by rfl⟩ : syracuseStep 1465381 = 274759) (by norm_num)
theorem B3300389 : Blo 1156638 3300389 := bbase (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) (by norm_num)
theorem B1301557 : Blo 1156638 1301557 := bbase (se 5 (by rfl) ⟨61010, by rfl⟩ : syracuseStep 1301557 = 122021) (by norm_num)
theorem B1301593 : Blo 1156638 1301593 := bbase (se 2 (by rfl) ⟨488097, by rfl⟩ : syracuseStep 1301593 = 976195) (by norm_num)
theorem B1236065 : Blo 1156638 1236065 := bbase (se 2 (by rfl) ⟨463524, by rfl⟩ : syracuseStep 1236065 = 927049) (by norm_num)
theorem B1956973 : Blo 1156638 1956973 := bbase (se 3 (by rfl) ⟨366932, by rfl⟩ : syracuseStep 1956973 = 733865) (by norm_num)
theorem B1301629 : Blo 1156638 1301629 := bbase (se 3 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 1301629 = 488111) (by norm_num)
theorem B1301665 : Blo 1156638 1301665 := bbase (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) (by norm_num)
theorem B1301701 : Blo 1156638 1301701 := bbase (se 4 (by rfl) ⟨122034, by rfl⟩ : syracuseStep 1301701 = 244069) (by norm_num)
theorem B1957061 : Blo 1156638 1957061 := bbase (se 4 (by rfl) ⟨183474, by rfl⟩ : syracuseStep 1957061 = 366949) (by norm_num)
theorem B1465553 : Blo 1156638 1465553 := bbase (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) (by norm_num)
theorem B1301737 : Blo 1156638 1301737 := bbase (se 2 (by rfl) ⟨488151, by rfl⟩ : syracuseStep 1301737 = 976303) (by norm_num)
theorem B2645245 : Blo 1156638 2645245 := bbase (se 3 (by rfl) ⟨495983, by rfl⟩ : syracuseStep 2645245 = 991967) (by norm_num)
theorem B1465609 : Blo 1156638 1465609 := bbase (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) (by norm_num)
theorem B1301773 : Blo 1156638 1301773 := bbase (se 3 (by rfl) ⟨244082, by rfl⟩ : syracuseStep 1301773 = 488165) (by norm_num)
theorem B1301809 : Blo 1156638 1301809 := bbase (se 2 (by rfl) ⟨488178, by rfl⟩ : syracuseStep 1301809 = 976357) (by norm_num)
theorem B1957189 : Blo 1156638 1957189 := bbase (se 4 (by rfl) ⟨183486, by rfl⟩ : syracuseStep 1957189 = 366973) (by norm_num)
theorem B1301845 : Blo 1156638 1301845 := bbase (se 11 (by rfl) ⟨953, by rfl⟩ : syracuseStep 1301845 = 1907) (by norm_num)
theorem B1236313 : Blo 1156638 1236313 := bbase (se 2 (by rfl) ⟨463617, by rfl⟩ : syracuseStep 1236313 = 927235) (by norm_num)
theorem B1465705 : Blo 1156638 1465705 := bbase (se 2 (by rfl) ⟨549639, by rfl⟩ : syracuseStep 1465705 = 1099279) (by norm_num)
theorem B2350453 : Blo 1156638 2350453 := bbase (se 5 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 2350453 = 220355) (by norm_num)
theorem B1301881 : Blo 1156638 1301881 := bbase (se 2 (by rfl) ⟨488205, by rfl⟩ : syracuseStep 1301881 = 976411) (by norm_num)
theorem B1301917 : Blo 1156638 1301917 := bbase (se 3 (by rfl) ⟨244109, by rfl⟩ : syracuseStep 1301917 = 488219) (by norm_num)
theorem B1957277 : Blo 1156638 1957277 := bbase (se 3 (by rfl) ⟨366989, by rfl⟩ : syracuseStep 1957277 = 733979) (by norm_num)
theorem B1301953 : Blo 1156638 1301953 := bbase (se 2 (by rfl) ⟨488232, by rfl⟩ : syracuseStep 1301953 = 976465) (by norm_num)
theorem B3300821 : Blo 1156638 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B1301989 : Blo 1156638 1301989 := bbase (se 4 (by rfl) ⟨122061, by rfl⟩ : syracuseStep 1301989 = 244123) (by norm_num)
theorem B1302025 : Blo 1156638 1302025 := bbase (se 2 (by rfl) ⟨488259, by rfl⟩ : syracuseStep 1302025 = 976519) (by norm_num)
theorem B1465877 : Blo 1156638 1465877 := bbase (se 6 (by rfl) ⟨34356, by rfl⟩ : syracuseStep 1465877 = 68713) (by norm_num)
theorem B1957405 : Blo 1156638 1957405 := bbase (se 3 (by rfl) ⟨367013, by rfl⟩ : syracuseStep 1957405 = 734027) (by norm_num)
theorem B1302061 : Blo 1156638 1302061 := bbase (se 3 (by rfl) ⟨244136, by rfl⟩ : syracuseStep 1302061 = 488273) (by norm_num)
theorem B1465933 : Blo 1156638 1465933 := bbase (se 3 (by rfl) ⟨274862, by rfl⟩ : syracuseStep 1465933 = 549725) (by norm_num)
theorem B1302097 : Blo 1156638 1302097 := bbase (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) (by norm_num)
theorem B1302133 : Blo 1156638 1302133 := bbase (se 5 (by rfl) ⟨61037, by rfl⟩ : syracuseStep 1302133 = 122075) (by norm_num)
theorem B1957493 : Blo 1156638 1957493 := bbase (se 5 (by rfl) ⟨91757, by rfl⟩ : syracuseStep 1957493 = 183515) (by norm_num)
theorem B1564309 : Blo 1156638 1564309 := bbase (se 6 (by rfl) ⟨36663, by rfl⟩ : syracuseStep 1564309 = 73327) (by norm_num)
theorem B1302169 : Blo 1156638 1302169 := bbase (se 2 (by rfl) ⟨488313, by rfl⟩ : syracuseStep 1302169 = 976627) (by norm_num)
theorem B1466029 : Blo 1156638 1466029 := bbase (se 3 (by rfl) ⟨274880, by rfl⟩ : syracuseStep 1466029 = 549761) (by norm_num)
theorem B1302205 : Blo 1156638 1302205 := bbase (se 3 (by rfl) ⟨244163, by rfl⟩ : syracuseStep 1302205 = 488327) (by norm_num)
theorem B1302241 : Blo 1156638 1302241 := bbase (se 2 (by rfl) ⟨488340, by rfl⟩ : syracuseStep 1302241 = 976681) (by norm_num)
theorem B1957621 : Blo 1156638 1957621 := bbase (se 5 (by rfl) ⟨91763, by rfl⟩ : syracuseStep 1957621 = 183527) (by norm_num)
theorem B1302277 : Blo 1156638 1302277 := bbase (se 4 (by rfl) ⟨122088, by rfl⟩ : syracuseStep 1302277 = 244177) (by norm_num)
theorem B1236745 : Blo 1156638 1236745 := bbase (se 2 (by rfl) ⟨463779, by rfl⟩ : syracuseStep 1236745 = 927559) (by norm_num)
theorem B4185877 : Blo 1156638 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B1302313 : Blo 1156638 1302313 := bbase (se 2 (by rfl) ⟨488367, by rfl⟩ : syracuseStep 1302313 = 976735) (by norm_num)
theorem B1302349 : Blo 1156638 1302349 := bbase (se 3 (by rfl) ⟨244190, by rfl⟩ : syracuseStep 1302349 = 488381) (by norm_num)
theorem B1957709 : Blo 1156638 1957709 := bbase (se 3 (by rfl) ⟨367070, by rfl⟩ : syracuseStep 1957709 = 734141) (by norm_num)
theorem B1236817 : Blo 1156638 1236817 := bbase (se 2 (by rfl) ⟨463806, by rfl⟩ : syracuseStep 1236817 = 927613) (by norm_num)
theorem B5857109 : Blo 1156638 5857109 := bbase (se 9 (by rfl) ⟨17159, by rfl⟩ : syracuseStep 5857109 = 34319) (by norm_num)
theorem B1466201 : Blo 1156638 1466201 := bbase (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) (by norm_num)
theorem B2350957 : Blo 1156638 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B1302385 : Blo 1156638 1302385 := bbase (se 2 (by rfl) ⟨488394, by rfl⟩ : syracuseStep 1302385 = 976789) (by norm_num)
theorem B1466257 : Blo 1156638 1466257 := bbase (se 2 (by rfl) ⟨549846, by rfl⟩ : syracuseStep 1466257 = 1099693) (by norm_num)
theorem B1302421 : Blo 1156638 1302421 := bbase (se 6 (by rfl) ⟨30525, by rfl⟩ : syracuseStep 1302421 = 61051) (by norm_num)
theorem B9887669 : Blo 1156638 9887669 := bbase (se 5 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 9887669 = 926969) (by norm_num)
theorem B1302457 : Blo 1156638 1302457 := bbase (se 2 (by rfl) ⟨488421, by rfl⟩ : syracuseStep 1302457 = 976843) (by norm_num)
theorem B1957837 : Blo 1156638 1957837 := bbase (se 3 (by rfl) ⟨367094, by rfl⟩ : syracuseStep 1957837 = 734189) (by norm_num)
theorem B2088917 : Blo 1156638 2088917 := bbase (se 7 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 2088917 = 48959) (by norm_num)
theorem B1302493 : Blo 1156638 1302493 := bbase (se 3 (by rfl) ⟨244217, by rfl⟩ : syracuseStep 1302493 = 488435) (by norm_num)
theorem B1466353 : Blo 1156638 1466353 := bbase (se 2 (by rfl) ⟨549882, by rfl⟩ : syracuseStep 1466353 = 1099765) (by norm_num)
theorem B1302529 : Blo 1156638 1302529 := bbase (se 2 (by rfl) ⟨488448, by rfl⟩ : syracuseStep 1302529 = 976897) (by norm_num)
theorem B1302565 : Blo 1156638 1302565 := bbase (se 4 (by rfl) ⟨122115, by rfl⟩ : syracuseStep 1302565 = 244231) (by norm_num)
theorem B1957925 : Blo 1156638 1957925 := bbase (se 4 (by rfl) ⟨183555, by rfl⟩ : syracuseStep 1957925 = 367111) (by norm_num)
theorem B1564741 : Blo 1156638 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B1302601 : Blo 1156638 1302601 := bbase (se 2 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 1302601 = 976951) (by norm_num)
theorem B1302637 : Blo 1156638 1302637 := bbase (se 3 (by rfl) ⟨244244, by rfl⟩ : syracuseStep 1302637 = 488489) (by norm_num)
theorem B2384005 : Blo 1156638 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1302673 : Blo 1156638 1302673 := bbase (se 2 (by rfl) ⟨488502, by rfl⟩ : syracuseStep 1302673 = 977005) (by norm_num)
theorem B1466525 : Blo 1156638 1466525 := bbase (se 3 (by rfl) ⟨274973, by rfl⟩ : syracuseStep 1466525 = 549947) (by norm_num)
theorem B1958053 : Blo 1156638 1958053 := bbase (se 4 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 1958053 = 367135) (by norm_num)
theorem B1302709 : Blo 1156638 1302709 := bbase (se 5 (by rfl) ⟨61064, by rfl⟩ : syracuseStep 1302709 = 122129) (by norm_num)
theorem B1237189 : Blo 1156638 1237189 := bbase (se 4 (by rfl) ⟨115986, by rfl⟩ : syracuseStep 1237189 = 231973) (by norm_num)
theorem B3301573 : Blo 1156638 3301573 := bbase (se 4 (by rfl) ⟨309522, by rfl⟩ : syracuseStep 3301573 = 619045) (by norm_num)
theorem B1466581 : Blo 1156638 1466581 := bbase (se 7 (by rfl) ⟨17186, by rfl⟩ : syracuseStep 1466581 = 34373) (by norm_num)
theorem B1302745 : Blo 1156638 1302745 := bbase (se 2 (by rfl) ⟨488529, by rfl⟩ : syracuseStep 1302745 = 977059) (by norm_num)
theorem B1302781 : Blo 1156638 1302781 := bbase (se 3 (by rfl) ⟨244271, by rfl⟩ : syracuseStep 1302781 = 488543) (by norm_num)
theorem B1958141 : Blo 1156638 1958141 := bbase (se 3 (by rfl) ⟨367151, by rfl⟩ : syracuseStep 1958141 = 734303) (by norm_num)
theorem B1302817 : Blo 1156638 1302817 := bbase (se 2 (by rfl) ⟨488556, by rfl⟩ : syracuseStep 1302817 = 977113) (by norm_num)
theorem B1466677 : Blo 1156638 1466677 := bbase (se 5 (by rfl) ⟨68750, by rfl⟩ : syracuseStep 1466677 = 137501) (by norm_num)
theorem B2974013 : Blo 1156638 2974013 := bbase (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) (by norm_num)
theorem B3760453 : Blo 1156638 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B1302853 : Blo 1156638 1302853 := bbase (se 4 (by rfl) ⟨122142, by rfl⟩ : syracuseStep 1302853 = 244285) (by norm_num)
theorem B2646341 : Blo 1156638 2646341 := bbase (se 4 (by rfl) ⟨248094, by rfl⟩ : syracuseStep 2646341 = 496189) (by norm_num)
theorem B1302889 : Blo 1156638 1302889 := bbase (se 2 (by rfl) ⟨488583, by rfl⟩ : syracuseStep 1302889 = 977167) (by norm_num)
theorem B1958269 : Blo 1156638 1958269 := bbase (se 3 (by rfl) ⟨367175, by rfl⟩ : syracuseStep 1958269 = 734351) (by norm_num)
theorem B1302925 : Blo 1156638 1302925 := bbase (se 3 (by rfl) ⟨244298, by rfl⟩ : syracuseStep 1302925 = 488597) (by norm_num)
theorem B2646413 : Blo 1156638 2646413 := bbase (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) (by norm_num)
theorem B8806805 : Blo 1156638 8806805 := bbase (se 6 (by rfl) ⟨206409, by rfl⟩ : syracuseStep 8806805 = 412819) (by norm_num)
theorem B1302961 : Blo 1156638 1302961 := bbase (se 2 (by rfl) ⟨488610, by rfl⟩ : syracuseStep 1302961 = 977221) (by norm_num)
theorem B1302997 : Blo 1156638 1302997 := bbase (se 7 (by rfl) ⟨15269, by rfl⟩ : syracuseStep 1302997 = 30539) (by norm_num)
theorem B1958357 : Blo 1156638 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B1466849 : Blo 1156638 1466849 := bbase (se 2 (by rfl) ⟨550068, by rfl⟩ : syracuseStep 1466849 = 1100137) (by norm_num)
theorem B1303033 : Blo 1156638 1303033 := bbase (se 2 (by rfl) ⟨488637, by rfl⟩ : syracuseStep 1303033 = 977275) (by norm_num)
theorem B1466905 : Blo 1156638 1466905 := bbase (se 2 (by rfl) ⟨550089, by rfl⟩ : syracuseStep 1466905 = 1100179) (by norm_num)
theorem B1303069 : Blo 1156638 1303069 := bbase (se 3 (by rfl) ⟨244325, by rfl⟩ : syracuseStep 1303069 = 488651) (by norm_num)
theorem B1237565 : Blo 1156638 1237565 := bbase (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) (by norm_num)
theorem B1303105 : Blo 1156638 1303105 := bbase (se 2 (by rfl) ⟨488664, by rfl⟩ : syracuseStep 1303105 = 977329) (by norm_num)
theorem B1958485 : Blo 1156638 1958485 := bbase (se 8 (by rfl) ⟨11475, by rfl⟩ : syracuseStep 1958485 = 22951) (by norm_num)
theorem B1303141 : Blo 1156638 1303141 := bbase (se 4 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 1303141 = 244339) (by norm_num)
theorem B1467001 : Blo 1156638 1467001 := bbase (se 2 (by rfl) ⟨550125, by rfl⟩ : syracuseStep 1467001 = 1100251) (by norm_num)
theorem B1237637 : Blo 1156638 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B1303177 : Blo 1156638 1303177 := bbase (se 2 (by rfl) ⟨488691, by rfl⟩ : syracuseStep 1303177 = 977383) (by norm_num)
theorem B1303213 : Blo 1156638 1303213 := bbase (se 3 (by rfl) ⟨244352, by rfl⟩ : syracuseStep 1303213 = 488705) (by norm_num)
theorem B1958573 : Blo 1156638 1958573 := bbase (se 3 (by rfl) ⟨367232, by rfl⟩ : syracuseStep 1958573 = 734465) (by norm_num)
theorem B7922357 : Blo 1156638 7922357 := bbase (se 5 (by rfl) ⟨371360, by rfl⟩ : syracuseStep 7922357 = 742721) (by norm_num)
theorem B1303249 : Blo 1156638 1303249 := bbase (se 2 (by rfl) ⟨488718, by rfl⟩ : syracuseStep 1303249 = 977437) (by norm_num)
theorem B1303285 : Blo 1156638 1303285 := bbase (se 5 (by rfl) ⟨61091, by rfl⟩ : syracuseStep 1303285 = 122183) (by norm_num)
theorem B1303321 : Blo 1156638 1303321 := bbase (se 2 (by rfl) ⟨488745, by rfl⟩ : syracuseStep 1303321 = 977491) (by norm_num)
theorem B1467173 : Blo 1156638 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B2089781 : Blo 1156638 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B1303357 : Blo 1156638 1303357 := bbase (se 3 (by rfl) ⟨244379, by rfl⟩ : syracuseStep 1303357 = 488759) (by norm_num)
theorem B1237825 : Blo 1156638 1237825 := bbase (se 2 (by rfl) ⟨464184, by rfl⟩ : syracuseStep 1237825 = 928369) (by norm_num)
theorem B1467229 : Blo 1156638 1467229 := bbase (se 3 (by rfl) ⟨275105, by rfl⟩ : syracuseStep 1467229 = 550211) (by norm_num)
theorem B1303393 : Blo 1156638 1303393 := bbase (se 2 (by rfl) ⟨488772, by rfl⟩ : syracuseStep 1303393 = 977545) (by norm_num)
theorem B1303429 : Blo 1156638 1303429 := bbase (se 4 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 1303429 = 244393) (by norm_num)
theorem B1303465 : Blo 1156638 1303465 := bbase (se 2 (by rfl) ⟨488799, by rfl⟩ : syracuseStep 1303465 = 977599) (by norm_num)
theorem B1467325 : Blo 1156638 1467325 := bbase (se 3 (by rfl) ⟨275123, by rfl⟩ : syracuseStep 1467325 = 550247) (by norm_num)
theorem B1303501 : Blo 1156638 1303501 := bbase (se 3 (by rfl) ⟨244406, by rfl⟩ : syracuseStep 1303501 = 488813) (by norm_num)
theorem B1172437 : Blo 1156638 1172437 := bbase (se 7 (by rfl) ⟨13739, by rfl⟩ : syracuseStep 1172437 = 27479) (by norm_num)
theorem B1303537 : Blo 1156638 1303537 := bbase (se 2 (by rfl) ⟨488826, by rfl⟩ : syracuseStep 1303537 = 977653) (by norm_num)
theorem B1238009 : Blo 1156638 1238009 := bbase (se 2 (by rfl) ⟨464253, by rfl⟩ : syracuseStep 1238009 = 928507) (by norm_num)
theorem B1303573 : Blo 1156638 1303573 := bbase (se 6 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 1303573 = 61105) (by norm_num)
theorem B1303609 : Blo 1156638 1303609 := bbase (se 2 (by rfl) ⟨488853, by rfl⟩ : syracuseStep 1303609 = 977707) (by norm_num)
theorem B1303645 : Blo 1156638 1303645 := bbase (se 3 (by rfl) ⟨244433, by rfl⟩ : syracuseStep 1303645 = 488867) (by norm_num)
theorem B5858405 : Blo 1156638 5858405 := bbase (se 4 (by rfl) ⟨549225, by rfl⟩ : syracuseStep 5858405 = 1098451) (by norm_num)
theorem B1467497 : Blo 1156638 1467497 := bbase (se 2 (by rfl) ⟨550311, by rfl⟩ : syracuseStep 1467497 = 1100623) (by norm_num)
theorem B1303681 : Blo 1156638 1303681 := bbase (se 2 (by rfl) ⟨488880, by rfl⟩ : syracuseStep 1303681 = 977761) (by norm_num)
theorem B1467553 : Blo 1156638 1467553 := bbase (se 2 (by rfl) ⟨550332, by rfl⟩ : syracuseStep 1467553 = 1100665) (by norm_num)
theorem B1303717 : Blo 1156638 1303717 := bbase (se 4 (by rfl) ⟨122223, by rfl⟩ : syracuseStep 1303717 = 244447) (by norm_num)
theorem B1303753 : Blo 1156638 1303753 := bbase (se 2 (by rfl) ⟨488907, by rfl⟩ : syracuseStep 1303753 = 977815) (by norm_num)
theorem B1303789 : Blo 1156638 1303789 := bbase (se 3 (by rfl) ⟨244460, by rfl⟩ : syracuseStep 1303789 = 488921) (by norm_num)
theorem B1467649 : Blo 1156638 1467649 := bbase (se 2 (by rfl) ⟨550368, by rfl⟩ : syracuseStep 1467649 = 1100737) (by norm_num)
theorem B1303825 : Blo 1156638 1303825 := bbase (se 2 (by rfl) ⟨488934, by rfl⟩ : syracuseStep 1303825 = 977869) (by norm_num)
theorem B1303861 : Blo 1156638 1303861 := bbase (se 5 (by rfl) ⟨61118, by rfl⟩ : syracuseStep 1303861 = 122237) (by norm_num)
theorem B1303897 : Blo 1156638 1303897 := bbase (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) (by norm_num)
theorem B1303933 : Blo 1156638 1303933 := bbase (se 3 (by rfl) ⟨244487, by rfl⟩ : syracuseStep 1303933 = 488975) (by norm_num)
theorem B1303969 : Blo 1156638 1303969 := bbase (se 2 (by rfl) ⟨488988, by rfl⟩ : syracuseStep 1303969 = 977977) (by norm_num)
theorem B2680229 : Blo 1156638 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B1467821 : Blo 1156638 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B4941253 : Blo 1156638 4941253 := bbase (se 4 (by rfl) ⟨463242, by rfl⟩ : syracuseStep 4941253 = 926485) (by norm_num)
theorem B1304005 : Blo 1156638 1304005 := bbase (se 4 (by rfl) ⟨122250, by rfl⟩ : syracuseStep 1304005 = 244501) (by norm_num)
theorem B1467877 : Blo 1156638 1467877 := bbase (se 4 (by rfl) ⟨137613, by rfl⟩ : syracuseStep 1467877 = 275227) (by norm_num)
theorem B1304041 : Blo 1156638 1304041 := bbase (se 2 (by rfl) ⟨489015, by rfl⟩ : syracuseStep 1304041 = 978031) (by norm_num)
theorem B1304077 : Blo 1156638 1304077 := bbase (se 3 (by rfl) ⟨244514, by rfl⟩ : syracuseStep 1304077 = 489029) (by norm_num)
theorem B1304113 : Blo 1156638 1304113 := bbase (se 2 (by rfl) ⟨489042, by rfl⟩ : syracuseStep 1304113 = 978085) (by norm_num)
theorem B1467973 : Blo 1156638 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B1304149 : Blo 1156638 1304149 := bbase (se 8 (by rfl) ⟨7641, by rfl⟩ : syracuseStep 1304149 = 15283) (by norm_num)
theorem B1304185 : Blo 1156638 1304185 := bbase (se 2 (by rfl) ⟨489069, by rfl⟩ : syracuseStep 1304185 = 978139) (by norm_num)
theorem B2352773 : Blo 1156638 2352773 := bbase (se 4 (by rfl) ⟨220572, by rfl⟩ : syracuseStep 2352773 = 441145) (by norm_num)
theorem B1304221 : Blo 1156638 1304221 := bbase (se 3 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 1304221 = 489083) (by norm_num)
theorem B1304257 : Blo 1156638 1304257 := bbase (se 2 (by rfl) ⟨489096, by rfl⟩ : syracuseStep 1304257 = 978193) (by norm_num)
theorem B1304293 : Blo 1156638 1304293 := bbase (se 4 (by rfl) ⟨122277, by rfl⟩ : syracuseStep 1304293 = 244555) (by norm_num)
theorem B1238761 : Blo 1156638 1238761 := bbase (se 2 (by rfl) ⟨464535, by rfl⟩ : syracuseStep 1238761 = 929071) (by norm_num)
theorem B1468145 : Blo 1156638 1468145 := bbase (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) (by norm_num)
theorem B3761909 : Blo 1156638 3761909 := bbase (se 5 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 3761909 = 352679) (by norm_num)
theorem B1304329 : Blo 1156638 1304329 := bbase (se 2 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 1304329 = 978247) (by norm_num)
theorem B1468201 : Blo 1156638 1468201 := bbase (se 2 (by rfl) ⟨550575, by rfl⟩ : syracuseStep 1468201 = 1101151) (by norm_num)
theorem B1304365 : Blo 1156638 1304365 := bbase (se 3 (by rfl) ⟨244568, by rfl⟩ : syracuseStep 1304365 = 489137) (by norm_num)
theorem B1238833 : Blo 1156638 1238833 := bbase (se 2 (by rfl) ⟨464562, by rfl⟩ : syracuseStep 1238833 = 929125) (by norm_num)
theorem B1304401 : Blo 1156638 1304401 := bbase (se 2 (by rfl) ⟨489150, by rfl⟩ : syracuseStep 1304401 = 978301) (by norm_num)
theorem B1304437 : Blo 1156638 1304437 := bbase (se 5 (by rfl) ⟨61145, by rfl⟩ : syracuseStep 1304437 = 122291) (by norm_num)
theorem B1468297 : Blo 1156638 1468297 := bbase (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) (by norm_num)
theorem B1304473 : Blo 1156638 1304473 := bbase (se 2 (by rfl) ⟨489177, by rfl⟩ : syracuseStep 1304473 = 978355) (by norm_num)
theorem B3008429 : Blo 1156638 3008429 := bbase (se 3 (by rfl) ⟨564080, by rfl⟩ : syracuseStep 3008429 = 1128161) (by norm_num)
theorem B1304509 : Blo 1156638 1304509 := bbase (se 3 (by rfl) ⟨244595, by rfl⟩ : syracuseStep 1304509 = 489191) (by norm_num)
theorem B1304545 : Blo 1156638 1304545 := bbase (se 2 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 1304545 = 978409) (by norm_num)
theorem B1239013 : Blo 1156638 1239013 := bbase (se 4 (by rfl) ⟨116157, by rfl⟩ : syracuseStep 1239013 = 232315) (by norm_num)
theorem B1304581 : Blo 1156638 1304581 := bbase (se 4 (by rfl) ⟨122304, by rfl⟩ : syracuseStep 1304581 = 244609) (by norm_num)
theorem B1304617 : Blo 1156638 1304617 := bbase (se 2 (by rfl) ⟨489231, by rfl⟩ : syracuseStep 1304617 = 978463) (by norm_num)
theorem B1468469 : Blo 1156638 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B1304653 : Blo 1156638 1304653 := bbase (se 3 (by rfl) ⟨244622, by rfl⟩ : syracuseStep 1304653 = 489245) (by norm_num)
theorem B2091109 : Blo 1156638 2091109 := bbase (se 4 (by rfl) ⟨196041, by rfl⟩ : syracuseStep 2091109 = 392083) (by norm_num)
theorem B1468525 : Blo 1156638 1468525 := bbase (se 3 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 1468525 = 550697) (by norm_num)
theorem B1304689 : Blo 1156638 1304689 := bbase (se 2 (by rfl) ⟨489258, by rfl⟩ : syracuseStep 1304689 = 978517) (by norm_num)
theorem B1304725 : Blo 1156638 1304725 := bbase (se 6 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 1304725 = 61159) (by norm_num)
theorem B1304761 : Blo 1156638 1304761 := bbase (se 2 (by rfl) ⟨489285, by rfl⟩ : syracuseStep 1304761 = 978571) (by norm_num)
theorem B1468621 : Blo 1156638 1468621 := bbase (se 3 (by rfl) ⟨275366, by rfl⟩ : syracuseStep 1468621 = 550733) (by norm_num)
theorem B1304797 : Blo 1156638 1304797 := bbase (se 3 (by rfl) ⟨244649, by rfl⟩ : syracuseStep 1304797 = 489299) (by norm_num)
theorem B2091253 : Blo 1156638 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B1304833 : Blo 1156638 1304833 := bbase (se 2 (by rfl) ⟨489312, by rfl⟩ : syracuseStep 1304833 = 978625) (by norm_num)
theorem B1304869 : Blo 1156638 1304869 := bbase (se 4 (by rfl) ⟨122331, by rfl⟩ : syracuseStep 1304869 = 244663) (by norm_num)
theorem B1304905 : Blo 1156638 1304905 := bbase (se 2 (by rfl) ⟨489339, by rfl⟩ : syracuseStep 1304905 = 978679) (by norm_num)
theorem B1173857 : Blo 1156638 1173857 := bbase (se 2 (by rfl) ⟨440196, by rfl⟩ : syracuseStep 1173857 = 880393) (by norm_num)
theorem B1304941 : Blo 1156638 1304941 := bbase (se 3 (by rfl) ⟨244676, by rfl⟩ : syracuseStep 1304941 = 489353) (by norm_num)
theorem B5859701 : Blo 1156638 5859701 := bbase (se 5 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 5859701 = 549347) (by norm_num)
theorem B1468793 : Blo 1156638 1468793 := bbase (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) (by norm_num)
theorem B1304977 : Blo 1156638 1304977 := bbase (se 2 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 1304977 = 978733) (by norm_num)
theorem B1468849 : Blo 1156638 1468849 := bbase (se 2 (by rfl) ⟨550818, by rfl⟩ : syracuseStep 1468849 = 1101637) (by norm_num)
theorem B1305013 : Blo 1156638 1305013 := bbase (se 5 (by rfl) ⟨61172, by rfl⟩ : syracuseStep 1305013 = 122345) (by norm_num)
theorem B1305049 : Blo 1156638 1305049 := bbase (se 2 (by rfl) ⟨489393, by rfl⟩ : syracuseStep 1305049 = 978787) (by norm_num)
theorem B1305085 : Blo 1156638 1305085 := bbase (se 3 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 1305085 = 489407) (by norm_num)
theorem B1305121 : Blo 1156638 1305121 := bbase (se 2 (by rfl) ⟨489420, by rfl⟩ : syracuseStep 1305121 = 978841) (by norm_num)
theorem B1305157 : Blo 1156638 1305157 := bbase (se 4 (by rfl) ⟨122358, by rfl⟩ : syracuseStep 1305157 = 244717) (by norm_num)
theorem B1305193 : Blo 1156638 1305193 := bbase (se 2 (by rfl) ⟨489447, by rfl⟩ : syracuseStep 1305193 = 978895) (by norm_num)
theorem B5565061 : Blo 1156638 5565061 := bbase (se 4 (by rfl) ⟨521724, by rfl⟩ : syracuseStep 5565061 = 1043449) (by norm_num)
theorem B1305229 : Blo 1156638 1305229 := bbase (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) (by norm_num)
theorem B1174181 : Blo 1156638 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B1305265 : Blo 1156638 1305265 := bbase (se 2 (by rfl) ⟨489474, by rfl⟩ : syracuseStep 1305265 = 978949) (by norm_num)
theorem B1305301 : Blo 1156638 1305301 := bbase (se 7 (by rfl) ⟨15296, by rfl⟩ : syracuseStep 1305301 = 30593) (by norm_num)
theorem B6253301 : Blo 1156638 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B1305337 : Blo 1156638 1305337 := bbase (se 2 (by rfl) ⟨489501, by rfl⟩ : syracuseStep 1305337 = 979003) (by norm_num)
theorem B1305373 : Blo 1156638 1305373 := bbase (se 3 (by rfl) ⟨244757, by rfl⟩ : syracuseStep 1305373 = 489515) (by norm_num)
theorem B1305409 : Blo 1156638 1305409 := bbase (se 2 (by rfl) ⟨489528, by rfl⟩ : syracuseStep 1305409 = 979057) (by norm_num)
theorem B1305445 : Blo 1156638 1305445 := bbase (se 4 (by rfl) ⟨122385, by rfl⟩ : syracuseStep 1305445 = 244771) (by norm_num)
theorem B1305481 : Blo 1156638 1305481 := bbase (se 2 (by rfl) ⟨489555, by rfl⟩ : syracuseStep 1305481 = 979111) (by norm_num)
theorem B4942741 : Blo 1156638 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B4942757 : Blo 1156638 4942757 := bbase (se 4 (by rfl) ⟨463383, by rfl⟩ : syracuseStep 4942757 = 926767) (by norm_num)
theorem B1305517 : Blo 1156638 1305517 := bbase (se 3 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 1305517 = 489569) (by norm_num)
theorem B1305553 : Blo 1156638 1305553 := bbase (se 2 (by rfl) ⟨489582, by rfl⟩ : syracuseStep 1305553 = 979165) (by norm_num)
theorem B3304421 : Blo 1156638 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B1305589 : Blo 1156638 1305589 := bbase (se 5 (by rfl) ⟨61199, by rfl⟩ : syracuseStep 1305589 = 122399) (by norm_num)
theorem B1305625 : Blo 1156638 1305625 := bbase (se 2 (by rfl) ⟨489609, by rfl⟩ : syracuseStep 1305625 = 979219) (by norm_num)
theorem B1305661 : Blo 1156638 1305661 := bbase (se 3 (by rfl) ⟨244811, by rfl⟩ : syracuseStep 1305661 = 489623) (by norm_num)
theorem B1305697 : Blo 1156638 1305697 := bbase (se 2 (by rfl) ⟨489636, by rfl⟩ : syracuseStep 1305697 = 979273) (by norm_num)
theorem B3009869 : Blo 1156638 3009869 := bbase (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) (by norm_num)
theorem B1175077 : Blo 1156638 1175077 := bbase (se 4 (by rfl) ⟨110163, by rfl⟩ : syracuseStep 1175077 = 220327) (by norm_num)
theorem B2780725 : Blo 1156638 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B5860997 : Blo 1156638 5860997 := bbase (se 4 (by rfl) ⟨549468, by rfl⟩ : syracuseStep 5860997 = 1098937) (by norm_num)
theorem B1175405 : Blo 1156638 1175405 := bbase (se 3 (by rfl) ⟨220388, by rfl⟩ : syracuseStep 1175405 = 440777) (by norm_num)
theorem B2715709 : Blo 1156638 2715709 := bbase (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) (by norm_num)
theorem B2781341 : Blo 1156638 2781341 := bbase (se 3 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 2781341 = 1043003) (by norm_num)
theorem B2781677 : Blo 1156638 2781677 := bbase (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) (by norm_num)
theorem B2257565 : Blo 1156638 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B2257573 : Blo 1156638 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B7533269 : Blo 1156638 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B2782069 : Blo 1156638 2782069 := bbase (se 5 (by rfl) ⟨130409, by rfl⟩ : syracuseStep 2782069 = 260819) (by norm_num)
theorem B1930133 : Blo 1156638 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B5862293 : Blo 1156638 5862293 := bbase (se 6 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 5862293 = 274795) (by norm_num)
theorem B7435253 : Blo 1156638 7435253 := bbase (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) (by norm_num)
theorem B4453381 : Blo 1156638 4453381 := bbase (se 4 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 4453381 = 835009) (by norm_num)
theorem B8909941 : Blo 1156638 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B4945013 : Blo 1156638 4945013 := bbase (se 5 (by rfl) ⟨231797, by rfl⟩ : syracuseStep 4945013 = 463595) (by norm_num)
theorem B2717093 : Blo 1156638 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B1504861 : Blo 1156638 1504861 := bbase (se 3 (by rfl) ⟨282161, by rfl⟩ : syracuseStep 1504861 = 564323) (by norm_num)
theorem B5568581 : Blo 1156638 5568581 := bbase (se 4 (by rfl) ⟨522054, by rfl⟩ : syracuseStep 5568581 = 1044109) (by norm_num)
theorem B5863589 : Blo 1156638 5863589 := bbase (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) (by norm_num)
theorem B1734965 : Blo 1156638 1734965 := bbase (se 5 (by rfl) ⟨81326, by rfl⟩ : syracuseStep 1734965 = 162653) (by norm_num)
theorem B1734989 : Blo 1156638 1734989 := bbase (se 3 (by rfl) ⟨325310, by rfl⟩ : syracuseStep 1734989 = 650621) (by norm_num)
theorem B1735013 : Blo 1156638 1735013 := bbase (se 4 (by rfl) ⟨162657, by rfl⟩ : syracuseStep 1735013 = 325315) (by norm_num)
theorem B1735037 : Blo 1156638 1735037 := bbase (se 3 (by rfl) ⟨325319, by rfl⟩ : syracuseStep 1735037 = 650639) (by norm_num)
theorem B1735061 : Blo 1156638 1735061 := bbase (se 6 (by rfl) ⟨40665, by rfl⟩ : syracuseStep 1735061 = 81331) (by norm_num)
theorem B1735085 : Blo 1156638 1735085 := bbase (se 3 (by rfl) ⟨325328, by rfl⟩ : syracuseStep 1735085 = 650657) (by norm_num)
theorem B1735109 : Blo 1156638 1735109 := bbase (se 4 (by rfl) ⟨162666, by rfl⟩ : syracuseStep 1735109 = 325333) (by norm_num)
theorem B1735133 : Blo 1156638 1735133 := bbase (se 3 (by rfl) ⟨325337, by rfl⟩ : syracuseStep 1735133 = 650675) (by norm_num)
theorem B1735157 : Blo 1156638 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B1735181 : Blo 1156638 1735181 := bbase (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) (by norm_num)
theorem B1735205 : Blo 1156638 1735205 := bbase (se 4 (by rfl) ⟨162675, by rfl⟩ : syracuseStep 1735205 = 325351) (by norm_num)
theorem B1735229 : Blo 1156638 1735229 := bbase (se 3 (by rfl) ⟨325355, by rfl⟩ : syracuseStep 1735229 = 650711) (by norm_num)
theorem B1735253 : Blo 1156638 1735253 := bbase (se 8 (by rfl) ⟨10167, by rfl⟩ : syracuseStep 1735253 = 20335) (by norm_num)
theorem B1735277 : Blo 1156638 1735277 := bbase (se 3 (by rfl) ⟨325364, by rfl⟩ : syracuseStep 1735277 = 650729) (by norm_num)
theorem B1735301 : Blo 1156638 1735301 := bbase (se 4 (by rfl) ⟨162684, by rfl⟩ : syracuseStep 1735301 = 325369) (by norm_num)
theorem B1735325 : Blo 1156638 1735325 := bbase (se 3 (by rfl) ⟨325373, by rfl⟩ : syracuseStep 1735325 = 650747) (by norm_num)
theorem B1735349 : Blo 1156638 1735349 := bbase (se 5 (by rfl) ⟨81344, by rfl⟩ : syracuseStep 1735349 = 162689) (by norm_num)
theorem B1735373 : Blo 1156638 1735373 := bbase (se 3 (by rfl) ⟨325382, by rfl⟩ : syracuseStep 1735373 = 650765) (by norm_num)
theorem B1735397 : Blo 1156638 1735397 := bbase (se 4 (by rfl) ⟨162693, by rfl⟩ : syracuseStep 1735397 = 325387) (by norm_num)
theorem B1735421 : Blo 1156638 1735421 := bbase (se 3 (by rfl) ⟨325391, by rfl⟩ : syracuseStep 1735421 = 650783) (by norm_num)
theorem B1735445 : Blo 1156638 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B5077781 : Blo 1156638 5077781 := bbase (se 6 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 5077781 = 238021) (by norm_num)
theorem B10582805 : Blo 1156638 10582805 := bbase (se 6 (by rfl) ⟨248034, by rfl⟩ : syracuseStep 10582805 = 496069) (by norm_num)
theorem B1735469 : Blo 1156638 1735469 := bbase (se 3 (by rfl) ⟨325400, by rfl⟩ : syracuseStep 1735469 = 650801) (by norm_num)
theorem B1735493 : Blo 1156638 1735493 := bbase (se 4 (by rfl) ⟨162702, by rfl⟩ : syracuseStep 1735493 = 325405) (by norm_num)
theorem B1735517 : Blo 1156638 1735517 := bbase (se 3 (by rfl) ⟨325409, by rfl⟩ : syracuseStep 1735517 = 650819) (by norm_num)
theorem B4455269 : Blo 1156638 4455269 := bbase (se 4 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 4455269 = 835363) (by norm_num)
theorem B1735541 : Blo 1156638 1735541 := bbase (se 5 (by rfl) ⟨81353, by rfl⟩ : syracuseStep 1735541 = 162707) (by norm_num)
theorem B1735565 : Blo 1156638 1735565 := bbase (se 3 (by rfl) ⟨325418, by rfl⟩ : syracuseStep 1735565 = 650837) (by norm_num)
theorem B1735589 : Blo 1156638 1735589 := bbase (se 4 (by rfl) ⟨162711, by rfl⟩ : syracuseStep 1735589 = 325423) (by norm_num)
theorem B1735613 : Blo 1156638 1735613 := bbase (se 3 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 1735613 = 650855) (by norm_num)
theorem B1735637 : Blo 1156638 1735637 := bbase (se 7 (by rfl) ⟨20339, by rfl⟩ : syracuseStep 1735637 = 40679) (by norm_num)
theorem B1735661 : Blo 1156638 1735661 := bbase (se 3 (by rfl) ⟨325436, by rfl⟩ : syracuseStep 1735661 = 650873) (by norm_num)
theorem B1735685 : Blo 1156638 1735685 := bbase (se 4 (by rfl) ⟨162720, by rfl⟩ : syracuseStep 1735685 = 325441) (by norm_num)
theorem B1735709 : Blo 1156638 1735709 := bbase (se 3 (by rfl) ⟨325445, by rfl⟩ : syracuseStep 1735709 = 650891) (by norm_num)
theorem B1735733 : Blo 1156638 1735733 := bbase (se 5 (by rfl) ⟨81362, by rfl⟩ : syracuseStep 1735733 = 162725) (by norm_num)
theorem B1735757 : Blo 1156638 1735757 := bbase (se 3 (by rfl) ⟨325454, by rfl⟩ : syracuseStep 1735757 = 650909) (by norm_num)
theorem B1735781 : Blo 1156638 1735781 := bbase (se 4 (by rfl) ⟨162729, by rfl⟩ : syracuseStep 1735781 = 325459) (by norm_num)
theorem B1735805 : Blo 1156638 1735805 := bbase (se 3 (by rfl) ⟨325463, by rfl⟩ : syracuseStep 1735805 = 650927) (by norm_num)
theorem B3013757 : Blo 1156638 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B1735829 : Blo 1156638 1735829 := bbase (se 6 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 1735829 = 81367) (by norm_num)
theorem B1735853 : Blo 1156638 1735853 := bbase (se 3 (by rfl) ⟨325472, by rfl⟩ : syracuseStep 1735853 = 650945) (by norm_num)
theorem B1735877 : Blo 1156638 1735877 := bbase (se 4 (by rfl) ⟨162738, by rfl⟩ : syracuseStep 1735877 = 325477) (by norm_num)
theorem B1735901 : Blo 1156638 1735901 := bbase (se 3 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 1735901 = 650963) (by norm_num)
theorem B1735925 : Blo 1156638 1735925 := bbase (se 5 (by rfl) ⟨81371, by rfl⟩ : syracuseStep 1735925 = 162743) (by norm_num)
theorem B1735949 : Blo 1156638 1735949 := bbase (se 3 (by rfl) ⟨325490, by rfl⟩ : syracuseStep 1735949 = 650981) (by norm_num)
theorem B2817301 : Blo 1156638 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B1735973 : Blo 1156638 1735973 := bbase (se 4 (by rfl) ⟨162747, by rfl⟩ : syracuseStep 1735973 = 325495) (by norm_num)
theorem B5569829 : Blo 1156638 5569829 := bbase (se 4 (by rfl) ⟨522171, by rfl⟩ : syracuseStep 5569829 = 1044343) (by norm_num)
theorem B1735997 : Blo 1156638 1735997 := bbase (se 3 (by rfl) ⟨325499, by rfl⟩ : syracuseStep 1735997 = 650999) (by norm_num)
theorem B1736021 : Blo 1156638 1736021 := bbase (se 11 (by rfl) ⟨1271, by rfl⟩ : syracuseStep 1736021 = 2543) (by norm_num)
theorem B1736045 : Blo 1156638 1736045 := bbase (se 3 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 1736045 = 651017) (by norm_num)
theorem B1736069 : Blo 1156638 1736069 := bbase (se 4 (by rfl) ⟨162756, by rfl⟩ : syracuseStep 1736069 = 325513) (by norm_num)
theorem B1736093 : Blo 1156638 1736093 := bbase (se 3 (by rfl) ⟨325517, by rfl⟩ : syracuseStep 1736093 = 651035) (by norm_num)
theorem B1736117 : Blo 1156638 1736117 := bbase (se 5 (by rfl) ⟨81380, by rfl⟩ : syracuseStep 1736117 = 162761) (by norm_num)
theorem B5864885 : Blo 1156638 5864885 := bbase (se 5 (by rfl) ⟨274916, by rfl⟩ : syracuseStep 5864885 = 549833) (by norm_num)
theorem B1736141 : Blo 1156638 1736141 := bbase (se 3 (by rfl) ⟨325526, by rfl⟩ : syracuseStep 1736141 = 651053) (by norm_num)
theorem B1736165 : Blo 1156638 1736165 := bbase (se 4 (by rfl) ⟨162765, by rfl⟩ : syracuseStep 1736165 = 325531) (by norm_num)
theorem B1736189 : Blo 1156638 1736189 := bbase (se 3 (by rfl) ⟨325535, by rfl⟩ : syracuseStep 1736189 = 651071) (by norm_num)
theorem B1736213 : Blo 1156638 1736213 := bbase (se 6 (by rfl) ⟨40692, by rfl⟩ : syracuseStep 1736213 = 81385) (by norm_num)
theorem B1736237 : Blo 1156638 1736237 := bbase (se 3 (by rfl) ⟨325544, by rfl⟩ : syracuseStep 1736237 = 651089) (by norm_num)
theorem B1736261 : Blo 1156638 1736261 := bbase (se 4 (by rfl) ⟨162774, by rfl⟩ : syracuseStep 1736261 = 325549) (by norm_num)
theorem B1736285 : Blo 1156638 1736285 := bbase (se 3 (by rfl) ⟨325553, by rfl⟩ : syracuseStep 1736285 = 651107) (by norm_num)
theorem B1736309 : Blo 1156638 1736309 := bbase (se 5 (by rfl) ⟨81389, by rfl⟩ : syracuseStep 1736309 = 162779) (by norm_num)
theorem B1736333 : Blo 1156638 1736333 := bbase (se 3 (by rfl) ⟨325562, by rfl⟩ : syracuseStep 1736333 = 651125) (by norm_num)
theorem B1736357 : Blo 1156638 1736357 := bbase (se 4 (by rfl) ⟨162783, by rfl⟩ : syracuseStep 1736357 = 325567) (by norm_num)
theorem B1736381 : Blo 1156638 1736381 := bbase (se 3 (by rfl) ⟨325571, by rfl⟩ : syracuseStep 1736381 = 651143) (by norm_num)
theorem B1736405 : Blo 1156638 1736405 := bbase (se 7 (by rfl) ⟨20348, by rfl⟩ : syracuseStep 1736405 = 40697) (by norm_num)
theorem B1736429 : Blo 1156638 1736429 := bbase (se 3 (by rfl) ⟨325580, by rfl⟩ : syracuseStep 1736429 = 651161) (by norm_num)
theorem B1736453 : Blo 1156638 1736453 := bbase (se 4 (by rfl) ⟨162792, by rfl⟩ : syracuseStep 1736453 = 325585) (by norm_num)
theorem B1736477 : Blo 1156638 1736477 := bbase (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) (by norm_num)
theorem B1408801 : Blo 1156638 1408801 := bbase (se 2 (by rfl) ⟨528300, by rfl⟩ : syracuseStep 1408801 = 1056601) (by norm_num)
theorem B1736501 : Blo 1156638 1736501 := bbase (se 5 (by rfl) ⟨81398, by rfl⟩ : syracuseStep 1736501 = 162797) (by norm_num)
theorem B1736525 : Blo 1156638 1736525 := bbase (se 3 (by rfl) ⟨325598, by rfl⟩ : syracuseStep 1736525 = 651197) (by norm_num)
theorem B1736549 : Blo 1156638 1736549 := bbase (se 4 (by rfl) ⟨162801, by rfl⟩ : syracuseStep 1736549 = 325603) (by norm_num)
theorem B1736573 : Blo 1156638 1736573 := bbase (se 3 (by rfl) ⟨325607, by rfl⟩ : syracuseStep 1736573 = 651215) (by norm_num)
theorem B1736597 : Blo 1156638 1736597 := bbase (se 6 (by rfl) ⟨40701, by rfl⟩ : syracuseStep 1736597 = 81403) (by norm_num)
theorem B1736621 : Blo 1156638 1736621 := bbase (se 3 (by rfl) ⟨325616, by rfl⟩ : syracuseStep 1736621 = 651233) (by norm_num)
theorem B2785213 : Blo 1156638 2785213 := bbase (se 3 (by rfl) ⟨522227, by rfl⟩ : syracuseStep 2785213 = 1044455) (by norm_num)
theorem B1736645 : Blo 1156638 1736645 := bbase (se 4 (by rfl) ⟨162810, by rfl⟩ : syracuseStep 1736645 = 325621) (by norm_num)
theorem B1736669 : Blo 1156638 1736669 := bbase (se 3 (by rfl) ⟨325625, by rfl⟩ : syracuseStep 1736669 = 651251) (by norm_num)
theorem B2785261 : Blo 1156638 2785261 := bbase (se 3 (by rfl) ⟨522236, by rfl⟩ : syracuseStep 2785261 = 1044473) (by norm_num)
theorem B1736693 : Blo 1156638 1736693 := bbase (se 5 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 1736693 = 162815) (by norm_num)
theorem B1736705 : Blo 1156638 1736705 := bstep (se 2 (by rfl) ⟨651264, by rfl⟩ : syracuseStep 1736705 = 1302529) B1302529
theorem B1736723 : Blo 1156638 1736723 := bstep (se 1 (by rfl) ⟨1302542, by rfl⟩ : syracuseStep 1736723 = 2605085) B2605085
theorem B1736753 : Blo 1156638 1736753 := bstep (se 2 (by rfl) ⟨651282, by rfl⟩ : syracuseStep 1736753 = 1302565) B1302565
theorem B1736771 : Blo 1156638 1736771 := bstep (se 1 (by rfl) ⟨1302578, by rfl⟩ : syracuseStep 1736771 = 2605157) B2605157
theorem B1736801 : Blo 1156638 1736801 := bstep (se 2 (by rfl) ⟨651300, by rfl⟩ : syracuseStep 1736801 = 1302601) B1302601
theorem B1736819 : Blo 1156638 1736819 := bstep (se 1 (by rfl) ⟨1302614, by rfl⟩ : syracuseStep 1736819 = 2605229) B2605229
theorem B1736849 : Blo 1156638 1736849 := bstep (se 2 (by rfl) ⟨651318, by rfl⟩ : syracuseStep 1736849 = 1302637) B1302637
theorem B1736867 : Blo 1156638 1736867 := bstep (se 1 (by rfl) ⟨1302650, by rfl⟩ : syracuseStep 1736867 = 2605301) B2605301
theorem B3178673 : Blo 1156638 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B1736897 : Blo 1156638 1736897 := bstep (se 2 (by rfl) ⟨651336, by rfl⟩ : syracuseStep 1736897 = 1302673) B1302673
theorem B1736915 : Blo 1156638 1736915 := bstep (se 1 (by rfl) ⟨1302686, by rfl⟩ : syracuseStep 1736915 = 2605373) B2605373
theorem B1736945 : Blo 1156638 1736945 := bstep (se 2 (by rfl) ⟨651354, by rfl⟩ : syracuseStep 1736945 = 1302709) B1302709
theorem B1736963 : Blo 1156638 1736963 := bstep (se 1 (by rfl) ⟨1302722, by rfl⟩ : syracuseStep 1736963 = 2605445) B2605445
theorem B1736993 : Blo 1156638 1736993 := bstep (se 2 (by rfl) ⟨651372, by rfl⟩ : syracuseStep 1736993 = 1302745) B1302745
theorem B4456739 : Blo 1156638 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B1737011 : Blo 1156638 1737011 := bstep (se 1 (by rfl) ⟨1302758, by rfl⟩ : syracuseStep 1737011 = 2605517) B2605517
theorem B1737041 : Blo 1156638 1737041 := bstep (se 2 (by rfl) ⟨651390, by rfl⟩ : syracuseStep 1737041 = 1302781) B1302781
theorem B1737059 : Blo 1156638 1737059 := bstep (se 1 (by rfl) ⟨1302794, by rfl⟩ : syracuseStep 1737059 = 2605589) B2605589
theorem B1737089 : Blo 1156638 1737089 := bstep (se 2 (by rfl) ⟨651408, by rfl⟩ : syracuseStep 1737089 = 1302817) B1302817
theorem B1737107 : Blo 1156638 1737107 := bstep (se 1 (by rfl) ⟨1302830, by rfl⟩ : syracuseStep 1737107 = 2605661) B2605661
theorem B5013937 : Blo 1156638 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B1737137 : Blo 1156638 1737137 := bstep (se 2 (by rfl) ⟨651426, by rfl⟩ : syracuseStep 1737137 = 1302853) B1302853
theorem B1737155 : Blo 1156638 1737155 := bstep (se 1 (by rfl) ⟨1302866, by rfl⟩ : syracuseStep 1737155 = 2605733) B2605733
theorem B1737185 : Blo 1156638 1737185 := bstep (se 2 (by rfl) ⟨651444, by rfl⟩ : syracuseStep 1737185 = 1302889) B1302889
theorem B1737203 : Blo 1156638 1737203 := bstep (se 1 (by rfl) ⟨1302902, by rfl⟩ : syracuseStep 1737203 = 2605805) B2605805
theorem B1737233 : Blo 1156638 1737233 := bstep (se 2 (by rfl) ⟨651462, by rfl⟩ : syracuseStep 1737233 = 1302925) B1302925
theorem B1737251 : Blo 1156638 1737251 := bstep (se 1 (by rfl) ⟨1302938, by rfl⟩ : syracuseStep 1737251 = 2605877) B2605877
theorem B5866019 : Blo 1156638 5866019 := bstep (se 1 (by rfl) ⟨4399514, by rfl⟩ : syracuseStep 5866019 = 8799029) B8799029
theorem B1737281 : Blo 1156638 1737281 := bstep (se 2 (by rfl) ⟨651480, by rfl⟩ : syracuseStep 1737281 = 1302961) B1302961
theorem B1737299 : Blo 1156638 1737299 := bstep (se 1 (by rfl) ⟨1302974, by rfl⟩ : syracuseStep 1737299 = 2605949) B2605949
theorem B2196067 : Blo 1156638 2196067 := bstep (se 1 (by rfl) ⟨1647050, by rfl⟩ : syracuseStep 2196067 = 3294101) B3294101
theorem B1737329 : Blo 1156638 1737329 := bstep (se 2 (by rfl) ⟨651498, by rfl⟩ : syracuseStep 1737329 = 1302997) B1302997
theorem B1737347 : Blo 1156638 1737347 := bstep (se 1 (by rfl) ⟨1303010, by rfl⟩ : syracuseStep 1737347 = 2606021) B2606021
theorem B1737377 : Blo 1156638 1737377 := bstep (se 2 (by rfl) ⟨651516, by rfl⟩ : syracuseStep 1737377 = 1303033) B1303033
theorem B1737395 : Blo 1156638 1737395 := bstep (se 1 (by rfl) ⟨1303046, by rfl⟩ : syracuseStep 1737395 = 2606093) B2606093
theorem B1737425 : Blo 1156638 1737425 := bstep (se 2 (by rfl) ⟨651534, by rfl⟩ : syracuseStep 1737425 = 1303069) B1303069
theorem B1737443 : Blo 1156638 1737443 := bstep (se 1 (by rfl) ⟨1303082, by rfl⟩ : syracuseStep 1737443 = 2606165) B2606165
theorem B1737473 : Blo 1156638 1737473 := bstep (se 2 (by rfl) ⟨651552, by rfl⟩ : syracuseStep 1737473 = 1303105) B1303105
theorem B2196227 : Blo 1156638 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B1737491 : Blo 1156638 1737491 := bstep (se 1 (by rfl) ⟨1303118, by rfl⟩ : syracuseStep 1737491 = 2606237) B2606237
theorem B4948771 : Blo 1156638 4948771 := bstep (se 1 (by rfl) ⟨3711578, by rfl⟩ : syracuseStep 4948771 = 7423157) B7423157
theorem B1737521 : Blo 1156638 1737521 := bstep (se 2 (by rfl) ⟨651570, by rfl⟩ : syracuseStep 1737521 = 1303141) B1303141
theorem B1737539 : Blo 1156638 1737539 := bstep (se 1 (by rfl) ⟨1303154, by rfl⟩ : syracuseStep 1737539 = 2606309) B2606309
theorem B1737569 : Blo 1156638 1737569 := bstep (se 2 (by rfl) ⟨651588, by rfl⟩ : syracuseStep 1737569 = 1303177) B1303177
theorem B1737587 : Blo 1156638 1737587 := bstep (se 1 (by rfl) ⟨1303190, by rfl⟩ : syracuseStep 1737587 = 2606381) B2606381
theorem B1737617 : Blo 1156638 1737617 := bstep (se 2 (by rfl) ⟨651606, by rfl⟩ : syracuseStep 1737617 = 1303213) B1303213
theorem B1737635 : Blo 1156638 1737635 := bstep (se 1 (by rfl) ⟨1303226, by rfl⟩ : syracuseStep 1737635 = 2606453) B2606453
theorem B1737665 : Blo 1156638 1737665 := bstep (se 2 (by rfl) ⟨651624, by rfl⟩ : syracuseStep 1737665 = 1303249) B1303249
theorem B1737683 : Blo 1156638 1737683 := bstep (se 1 (by rfl) ⟨1303262, by rfl⟩ : syracuseStep 1737683 = 2606525) B2606525
theorem B4391921 : Blo 1156638 4391921 := bstep (se 2 (by rfl) ⟨1646970, by rfl⟩ : syracuseStep 4391921 = 3293941) B3293941
theorem B1737713 : Blo 1156638 1737713 := bstep (se 2 (by rfl) ⟨651642, by rfl⟩ : syracuseStep 1737713 = 1303285) B1303285
theorem B1737731 : Blo 1156638 1737731 := bstep (se 1 (by rfl) ⟨1303298, by rfl⟩ : syracuseStep 1737731 = 2606597) B2606597
theorem B1737761 : Blo 1156638 1737761 := bstep (se 2 (by rfl) ⟨651660, by rfl⟩ : syracuseStep 1737761 = 1303321) B1303321
theorem B1737779 : Blo 1156638 1737779 := bstep (se 1 (by rfl) ⟨1303334, by rfl⟩ : syracuseStep 1737779 = 2606669) B2606669
theorem B1737809 : Blo 1156638 1737809 := bstep (se 2 (by rfl) ⟨651678, by rfl⟩ : syracuseStep 1737809 = 1303357) B1303357
theorem B1737827 : Blo 1156638 1737827 := bstep (se 1 (by rfl) ⟨1303370, by rfl⟩ : syracuseStep 1737827 = 2606741) B2606741
theorem B1737857 : Blo 1156638 1737857 := bstep (se 2 (by rfl) ⟨651696, by rfl⟩ : syracuseStep 1737857 = 1303393) B1303393
theorem B1737875 : Blo 1156638 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B1737905 : Blo 1156638 1737905 := bstep (se 2 (by rfl) ⟨651714, by rfl⟩ : syracuseStep 1737905 = 1303429) B1303429
theorem B1737923 : Blo 1156638 1737923 := bstep (se 1 (by rfl) ⟨1303442, by rfl⟩ : syracuseStep 1737923 = 2606885) B2606885
theorem B6685901 : Blo 1156638 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B1737953 : Blo 1156638 1737953 := bstep (se 2 (by rfl) ⟨651732, by rfl⟩ : syracuseStep 1737953 = 1303465) B1303465
theorem B1737971 : Blo 1156638 1737971 := bstep (se 1 (by rfl) ⟨1303478, by rfl⟩ : syracuseStep 1737971 = 2606957) B2606957
theorem B1738001 : Blo 1156638 1738001 := bstep (se 2 (by rfl) ⟨651750, by rfl⟩ : syracuseStep 1738001 = 1303501) B1303501
theorem B1738019 : Blo 1156638 1738019 := bstep (se 1 (by rfl) ⟨1303514, by rfl⟩ : syracuseStep 1738019 = 2607029) B2607029
theorem B1738049 : Blo 1156638 1738049 := bstep (se 2 (by rfl) ⟨651768, by rfl⟩ : syracuseStep 1738049 = 1303537) B1303537
theorem B5866829 : Blo 1156638 5866829 := bstep (se 3 (by rfl) ⟨1100030, by rfl⟩ : syracuseStep 5866829 = 2200061) B2200061
theorem B1738067 : Blo 1156638 1738067 := bstep (se 1 (by rfl) ⟨1303550, by rfl⟩ : syracuseStep 1738067 = 2607101) B2607101
theorem B2229617 : Blo 1156638 2229617 := bstep (se 2 (by rfl) ⟨836106, by rfl⟩ : syracuseStep 2229617 = 1672213) B1672213
theorem B1738097 : Blo 1156638 1738097 := bstep (se 2 (by rfl) ⟨651786, by rfl⟩ : syracuseStep 1738097 = 1303573) B1303573
theorem B1738115 : Blo 1156638 1738115 := bstep (se 1 (by rfl) ⟨1303586, by rfl⟩ : syracuseStep 1738115 = 2607173) B2607173
theorem B56460685 : Blo 1156638 56460685 := bstep (se 3 (by rfl) ⟨10586378, by rfl⟩ : syracuseStep 56460685 = 21172757) B21172757
theorem B1738145 : Blo 1156638 1738145 := bstep (se 2 (by rfl) ⟨651804, by rfl⟩ : syracuseStep 1738145 = 1303609) B1303609
theorem B1738163 : Blo 1156638 1738163 := bstep (se 1 (by rfl) ⟨1303622, by rfl⟩ : syracuseStep 1738163 = 2607245) B2607245
theorem B1738193 : Blo 1156638 1738193 := bstep (se 2 (by rfl) ⟨651822, by rfl⟩ : syracuseStep 1738193 = 1303645) B1303645
theorem B1738211 : Blo 1156638 1738211 := bstep (se 1 (by rfl) ⟨1303658, by rfl⟩ : syracuseStep 1738211 = 2607317) B2607317
theorem B1738241 : Blo 1156638 1738241 := bstep (se 2 (by rfl) ⟨651840, by rfl⟩ : syracuseStep 1738241 = 1303681) B1303681
theorem B1738259 : Blo 1156638 1738259 := bstep (se 1 (by rfl) ⟨1303694, by rfl⟩ : syracuseStep 1738259 = 2607389) B2607389
theorem B1738289 : Blo 1156638 1738289 := bstep (se 2 (by rfl) ⟨651858, by rfl⟩ : syracuseStep 1738289 = 1303717) B1303717
theorem B1738307 : Blo 1156638 1738307 := bstep (se 1 (by rfl) ⟨1303730, by rfl⟩ : syracuseStep 1738307 = 2607461) B2607461
theorem B1738337 : Blo 1156638 1738337 := bstep (se 2 (by rfl) ⟨651876, by rfl⟩ : syracuseStep 1738337 = 1303753) B1303753
theorem B1738355 : Blo 1156638 1738355 := bstep (se 1 (by rfl) ⟨1303766, by rfl⟩ : syracuseStep 1738355 = 2607533) B2607533
theorem B4392589 : Blo 1156638 4392589 := bstep (se 3 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 4392589 = 1647221) B1647221
theorem B1738385 : Blo 1156638 1738385 := bstep (se 2 (by rfl) ⟨651894, by rfl⟩ : syracuseStep 1738385 = 1303789) B1303789
theorem B1672849 : Blo 1156638 1672849 := bstep (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) B1254637
theorem B1738403 : Blo 1156638 1738403 := bstep (se 1 (by rfl) ⟨1303802, by rfl⟩ : syracuseStep 1738403 = 2607605) B2607605
theorem B1738433 : Blo 1156638 1738433 := bstep (se 2 (by rfl) ⟨651912, by rfl⟩ : syracuseStep 1738433 = 1303825) B1303825
theorem B1738451 : Blo 1156638 1738451 := bstep (se 1 (by rfl) ⟨1303838, by rfl⟩ : syracuseStep 1738451 = 2607677) B2607677
theorem B1738481 : Blo 1156638 1738481 := bstep (se 2 (by rfl) ⟨651930, by rfl⟩ : syracuseStep 1738481 = 1303861) B1303861
theorem B1738499 : Blo 1156638 1738499 := bstep (se 1 (by rfl) ⟨1303874, by rfl⟩ : syracuseStep 1738499 = 2607749) B2607749
theorem B1738529 : Blo 1156638 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B2197297 : Blo 1156638 2197297 := bstep (se 2 (by rfl) ⟨823986, by rfl⟩ : syracuseStep 2197297 = 1647973) B1647973
theorem B1738547 : Blo 1156638 1738547 := bstep (se 1 (by rfl) ⟨1303910, by rfl⟩ : syracuseStep 1738547 = 2607821) B2607821
theorem B1738577 : Blo 1156638 1738577 := bstep (se 2 (by rfl) ⟨651966, by rfl⟩ : syracuseStep 1738577 = 1303933) B1303933
theorem B1738595 : Blo 1156638 1738595 := bstep (se 1 (by rfl) ⟨1303946, by rfl⟩ : syracuseStep 1738595 = 2607893) B2607893
theorem B1738625 : Blo 1156638 1738625 := bstep (se 2 (by rfl) ⟨651984, by rfl⟩ : syracuseStep 1738625 = 1303969) B1303969
theorem B1738643 : Blo 1156638 1738643 := bstep (se 1 (by rfl) ⟨1303982, by rfl⟩ : syracuseStep 1738643 = 2607965) B2607965
theorem B6588337 : Blo 1156638 6588337 := bstep (se 2 (by rfl) ⟨2470626, by rfl⟩ : syracuseStep 6588337 = 4941253) B4941253
theorem B1738673 : Blo 1156638 1738673 := bstep (se 2 (by rfl) ⟨652002, by rfl⟩ : syracuseStep 1738673 = 1304005) B1304005
theorem B1738691 : Blo 1156638 1738691 := bstep (se 1 (by rfl) ⟨1304018, by rfl⟩ : syracuseStep 1738691 = 2608037) B2608037
theorem B1738721 : Blo 1156638 1738721 := bstep (se 2 (by rfl) ⟨652020, by rfl⟩ : syracuseStep 1738721 = 1304041) B1304041
theorem B4950001 : Blo 1156638 4950001 := bstep (se 2 (by rfl) ⟨1856250, by rfl⟩ : syracuseStep 4950001 = 3712501) B3712501
theorem B1738739 : Blo 1156638 1738739 := bstep (se 1 (by rfl) ⟨1304054, by rfl⟩ : syracuseStep 1738739 = 2608109) B2608109
theorem B1738769 : Blo 1156638 1738769 := bstep (se 2 (by rfl) ⟨652038, by rfl⟩ : syracuseStep 1738769 = 1304077) B1304077
theorem B1738787 : Blo 1156638 1738787 := bstep (se 1 (by rfl) ⟨1304090, by rfl⟩ : syracuseStep 1738787 = 2608181) B2608181
theorem B1738817 : Blo 1156638 1738817 := bstep (se 2 (by rfl) ⟨652056, by rfl⟩ : syracuseStep 1738817 = 1304113) B1304113
theorem B1738835 : Blo 1156638 1738835 := bstep (se 1 (by rfl) ⟨1304126, by rfl⟩ : syracuseStep 1738835 = 2608253) B2608253
theorem B1738865 : Blo 1156638 1738865 := bstep (se 2 (by rfl) ⟨652074, by rfl⟩ : syracuseStep 1738865 = 1304149) B1304149
theorem B1738883 : Blo 1156638 1738883 := bstep (se 1 (by rfl) ⟨1304162, by rfl⟩ : syracuseStep 1738883 = 2608325) B2608325
theorem B1738913 : Blo 1156638 1738913 := bstep (se 2 (by rfl) ⟨652092, by rfl⟩ : syracuseStep 1738913 = 1304185) B1304185
theorem B1738931 : Blo 1156638 1738931 := bstep (se 1 (by rfl) ⟨1304198, by rfl⟩ : syracuseStep 1738931 = 2608397) B2608397
theorem B1738961 : Blo 1156638 1738961 := bstep (se 2 (by rfl) ⟨652110, by rfl⟩ : syracuseStep 1738961 = 1304221) B1304221
theorem B1738979 : Blo 1156638 1738979 := bstep (se 1 (by rfl) ⟨1304234, by rfl⟩ : syracuseStep 1738979 = 2608469) B2608469
theorem B1739009 : Blo 1156638 1739009 := bstep (se 2 (by rfl) ⟨652128, by rfl⟩ : syracuseStep 1739009 = 1304257) B1304257
theorem B1739027 : Blo 1156638 1739027 := bstep (se 1 (by rfl) ⟨1304270, by rfl⟩ : syracuseStep 1739027 = 2608541) B2608541
theorem B1739057 : Blo 1156638 1739057 := bstep (se 2 (by rfl) ⟨652146, by rfl⟩ : syracuseStep 1739057 = 1304293) B1304293
theorem B1739075 : Blo 1156638 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B1739105 : Blo 1156638 1739105 := bstep (se 2 (by rfl) ⟨652164, by rfl⟩ : syracuseStep 1739105 = 1304329) B1304329
theorem B1739123 : Blo 1156638 1739123 := bstep (se 1 (by rfl) ⟨1304342, by rfl⟩ : syracuseStep 1739123 = 2608685) B2608685
theorem B5147021 : Blo 1156638 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B1673617 : Blo 1156638 1673617 := bstep (se 2 (by rfl) ⟨627606, by rfl⟩ : syracuseStep 1673617 = 1255213) B1255213
theorem B1739153 : Blo 1156638 1739153 := bstep (se 2 (by rfl) ⟨652182, by rfl⟩ : syracuseStep 1739153 = 1304365) B1304365
theorem B4393379 : Blo 1156638 4393379 := bstep (se 1 (by rfl) ⟨3295034, by rfl⟩ : syracuseStep 4393379 = 6590069) B6590069
theorem B1739171 : Blo 1156638 1739171 := bstep (se 1 (by rfl) ⟨1304378, by rfl⟩ : syracuseStep 1739171 = 2608757) B2608757
theorem B1739201 : Blo 1156638 1739201 := bstep (se 2 (by rfl) ⟨652200, by rfl⟩ : syracuseStep 1739201 = 1304401) B1304401
theorem B1739219 : Blo 1156638 1739219 := bstep (se 1 (by rfl) ⟨1304414, by rfl⟩ : syracuseStep 1739219 = 2608829) B2608829
theorem B1739249 : Blo 1156638 1739249 := bstep (se 2 (by rfl) ⟨652218, by rfl⟩ : syracuseStep 1739249 = 1304437) B1304437
theorem B1739267 : Blo 1156638 1739267 := bstep (se 1 (by rfl) ⟨1304450, by rfl⟩ : syracuseStep 1739267 = 2608901) B2608901
theorem B1739297 : Blo 1156638 1739297 := bstep (se 2 (by rfl) ⟨652236, by rfl⟩ : syracuseStep 1739297 = 1304473) B1304473
theorem B2787875 : Blo 1156638 2787875 := bstep (se 1 (by rfl) ⟨2090906, by rfl⟩ : syracuseStep 2787875 = 4181813) B4181813
theorem B1739315 : Blo 1156638 1739315 := bstep (se 1 (by rfl) ⟨1304486, by rfl⟩ : syracuseStep 1739315 = 2608973) B2608973
theorem B1739345 : Blo 1156638 1739345 := bstep (se 2 (by rfl) ⟨652254, by rfl⟩ : syracuseStep 1739345 = 1304509) B1304509
theorem B1739363 : Blo 1156638 1739363 := bstep (se 1 (by rfl) ⟨1304522, by rfl⟩ : syracuseStep 1739363 = 2609045) B2609045
theorem B1739393 : Blo 1156638 1739393 := bstep (se 2 (by rfl) ⟨652272, by rfl⟩ : syracuseStep 1739393 = 1304545) B1304545
theorem B19827341 : Blo 1156638 19827341 := bstep (se 3 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 19827341 = 7435253) B7435253
theorem B1739411 : Blo 1156638 1739411 := bstep (se 1 (by rfl) ⟨1304558, by rfl⟩ : syracuseStep 1739411 = 2609117) B2609117
theorem B1739441 : Blo 1156638 1739441 := bstep (se 2 (by rfl) ⟨652290, by rfl⟩ : syracuseStep 1739441 = 1304581) B1304581
theorem B1739459 : Blo 1156638 1739459 := bstep (se 1 (by rfl) ⟨1304594, by rfl⟩ : syracuseStep 1739459 = 2609189) B2609189
theorem B1673939 : Blo 1156638 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B1739489 : Blo 1156638 1739489 := bstep (se 2 (by rfl) ⟨652308, by rfl⟩ : syracuseStep 1739489 = 1304617) B1304617
theorem B2788067 : Blo 1156638 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B1739507 : Blo 1156638 1739507 := bstep (se 1 (by rfl) ⟨1304630, by rfl⟩ : syracuseStep 1739507 = 2609261) B2609261
theorem B1739537 : Blo 1156638 1739537 := bstep (se 2 (by rfl) ⟨652326, by rfl⟩ : syracuseStep 1739537 = 1304653) B1304653
theorem B1739555 : Blo 1156638 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B2788145 : Blo 1156638 2788145 := bstep (se 2 (by rfl) ⟨1045554, by rfl⟩ : syracuseStep 2788145 = 2091109) B2091109
theorem B1739585 : Blo 1156638 1739585 := bstep (se 2 (by rfl) ⟨652344, by rfl⟩ : syracuseStep 1739585 = 1304689) B1304689
theorem B2198353 : Blo 1156638 2198353 := bstep (se 2 (by rfl) ⟨824382, by rfl⟩ : syracuseStep 2198353 = 1648765) B1648765
theorem B1739603 : Blo 1156638 1739603 := bstep (se 1 (by rfl) ⟨1304702, by rfl⟩ : syracuseStep 1739603 = 2609405) B2609405
theorem B1739633 : Blo 1156638 1739633 := bstep (se 2 (by rfl) ⟨652362, by rfl⟩ : syracuseStep 1739633 = 1304725) B1304725
theorem B1739651 : Blo 1156638 1739651 := bstep (se 1 (by rfl) ⟨1304738, by rfl⟩ : syracuseStep 1739651 = 2609477) B2609477
theorem B3345293 : Blo 1156638 3345293 := bstep (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) B1254485
theorem B1739681 : Blo 1156638 1739681 := bstep (se 2 (by rfl) ⟨652380, by rfl⟩ : syracuseStep 1739681 = 1304761) B1304761
theorem B1739699 : Blo 1156638 1739699 := bstep (se 1 (by rfl) ⟨1304774, by rfl⟩ : syracuseStep 1739699 = 2609549) B2609549
theorem B1739729 : Blo 1156638 1739729 := bstep (se 2 (by rfl) ⟨652398, by rfl⟩ : syracuseStep 1739729 = 1304797) B1304797
theorem B1739747 : Blo 1156638 1739747 := bstep (se 1 (by rfl) ⟨1304810, by rfl⟩ : syracuseStep 1739747 = 2609621) B2609621
theorem B2788337 : Blo 1156638 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B1739777 : Blo 1156638 1739777 := bstep (se 2 (by rfl) ⟨652416, by rfl⟩ : syracuseStep 1739777 = 1304833) B1304833
theorem B1739795 : Blo 1156638 1739795 := bstep (se 1 (by rfl) ⟨1304846, by rfl⟩ : syracuseStep 1739795 = 2609693) B2609693
theorem B4394033 : Blo 1156638 4394033 := bstep (se 2 (by rfl) ⟨1647762, by rfl⟩ : syracuseStep 4394033 = 3295525) B3295525
theorem B1739825 : Blo 1156638 1739825 := bstep (se 2 (by rfl) ⟨652434, by rfl⟩ : syracuseStep 1739825 = 1304869) B1304869
theorem B1739843 : Blo 1156638 1739843 := bstep (se 1 (by rfl) ⟨1304882, by rfl⟩ : syracuseStep 1739843 = 2609765) B2609765
theorem B1739873 : Blo 1156638 1739873 := bstep (se 2 (by rfl) ⟨652452, by rfl⟩ : syracuseStep 1739873 = 1304905) B1304905
theorem B1739891 : Blo 1156638 1739891 := bstep (se 1 (by rfl) ⟨1304918, by rfl⟩ : syracuseStep 1739891 = 2609837) B2609837
theorem B1739921 : Blo 1156638 1739921 := bstep (se 2 (by rfl) ⟨652470, by rfl⟩ : syracuseStep 1739921 = 1304941) B1304941
theorem B1739939 : Blo 1156638 1739939 := bstep (se 1 (by rfl) ⟨1304954, by rfl⟩ : syracuseStep 1739939 = 2609909) B2609909
theorem B1739969 : Blo 1156638 1739969 := bstep (se 2 (by rfl) ⟨652488, by rfl⟩ : syracuseStep 1739969 = 1304977) B1304977
theorem B3968195 : Blo 1156638 3968195 := bstep (se 1 (by rfl) ⟨2976146, by rfl⟩ : syracuseStep 3968195 = 5952293) B5952293
theorem B1739987 : Blo 1156638 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B2198755 : Blo 1156638 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B1740017 : Blo 1156638 1740017 := bstep (se 2 (by rfl) ⟨652506, by rfl⟩ : syracuseStep 1740017 = 1305013) B1305013
theorem B1740035 : Blo 1156638 1740035 := bstep (se 1 (by rfl) ⟨1305026, by rfl⟩ : syracuseStep 1740035 = 2610053) B2610053
theorem B1674499 : Blo 1156638 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B2198801 : Blo 1156638 2198801 := bstep (se 2 (by rfl) ⟨824550, by rfl⟩ : syracuseStep 2198801 = 1649101) B1649101
theorem B1740065 : Blo 1156638 1740065 := bstep (se 2 (by rfl) ⟨652524, by rfl⟩ : syracuseStep 1740065 = 1305049) B1305049
theorem B1740083 : Blo 1156638 1740083 := bstep (se 1 (by rfl) ⟨1305062, by rfl⟩ : syracuseStep 1740083 = 2610125) B2610125
theorem B1740113 : Blo 1156638 1740113 := bstep (se 2 (by rfl) ⟨652542, by rfl⟩ : syracuseStep 1740113 = 1305085) B1305085
theorem B6589795 : Blo 1156638 6589795 := bstep (se 1 (by rfl) ⟨4942346, by rfl⟩ : syracuseStep 6589795 = 9884693) B9884693
theorem B1740131 : Blo 1156638 1740131 := bstep (se 1 (by rfl) ⟨1305098, by rfl⟩ : syracuseStep 1740131 = 2610197) B2610197
theorem B1740161 : Blo 1156638 1740161 := bstep (se 2 (by rfl) ⟨652560, by rfl⟩ : syracuseStep 1740161 = 1305121) B1305121
theorem B1740179 : Blo 1156638 1740179 := bstep (se 1 (by rfl) ⟨1305134, by rfl⟩ : syracuseStep 1740179 = 2610269) B2610269
theorem B1740209 : Blo 1156638 1740209 := bstep (se 2 (by rfl) ⟨652578, by rfl⟩ : syracuseStep 1740209 = 1305157) B1305157
theorem B1740227 : Blo 1156638 1740227 := bstep (se 1 (by rfl) ⟨1305170, by rfl⟩ : syracuseStep 1740227 = 2610341) B2610341
theorem B1740257 : Blo 1156638 1740257 := bstep (se 2 (by rfl) ⟨652596, by rfl⟩ : syracuseStep 1740257 = 1305193) B1305193
theorem B1740275 : Blo 1156638 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B8785421 : Blo 1156638 8785421 := bstep (se 3 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 8785421 = 3294533) B3294533
theorem B1740305 : Blo 1156638 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B1740323 : Blo 1156638 1740323 := bstep (se 1 (by rfl) ⟨1305242, by rfl⟩ : syracuseStep 1740323 = 2610485) B2610485
theorem B2199089 : Blo 1156638 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B1740353 : Blo 1156638 1740353 := bstep (se 2 (by rfl) ⟨652632, by rfl⟩ : syracuseStep 1740353 = 1305265) B1305265
theorem B1740371 : Blo 1156638 1740371 := bstep (se 1 (by rfl) ⟨1305278, by rfl⟩ : syracuseStep 1740371 = 2610557) B2610557
theorem B1740401 : Blo 1156638 1740401 := bstep (se 2 (by rfl) ⟨652650, by rfl⟩ : syracuseStep 1740401 = 1305301) B1305301
theorem B42929777 : Blo 1156638 42929777 := bstep (se 2 (by rfl) ⟨16098666, by rfl⟩ : syracuseStep 42929777 = 32197333) B32197333
theorem B1740419 : Blo 1156638 1740419 := bstep (se 1 (by rfl) ⟨1305314, by rfl⟩ : syracuseStep 1740419 = 2610629) B2610629
theorem B1740449 : Blo 1156638 1740449 := bstep (se 2 (by rfl) ⟨652668, by rfl⟩ : syracuseStep 1740449 = 1305337) B1305337
theorem B1740467 : Blo 1156638 1740467 := bstep (se 1 (by rfl) ⟨1305350, by rfl⟩ : syracuseStep 1740467 = 2610701) B2610701
theorem B1740497 : Blo 1156638 1740497 := bstep (se 2 (by rfl) ⟨652686, by rfl⟩ : syracuseStep 1740497 = 1305373) B1305373
theorem B1740515 : Blo 1156638 1740515 := bstep (se 1 (by rfl) ⟨1305386, by rfl⟩ : syracuseStep 1740515 = 2610773) B2610773
theorem B1740545 : Blo 1156638 1740545 := bstep (se 2 (by rfl) ⟨652704, by rfl⟩ : syracuseStep 1740545 = 1305409) B1305409
theorem B7147277 : Blo 1156638 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B1740563 : Blo 1156638 1740563 := bstep (se 1 (by rfl) ⟨1305422, by rfl⟩ : syracuseStep 1740563 = 2610845) B2610845
theorem B1740593 : Blo 1156638 1740593 := bstep (se 2 (by rfl) ⟨652722, by rfl⟩ : syracuseStep 1740593 = 1305445) B1305445
theorem B1740611 : Blo 1156638 1740611 := bstep (se 1 (by rfl) ⟨1305458, by rfl⟩ : syracuseStep 1740611 = 2610917) B2610917
theorem B1740641 : Blo 1156638 1740641 := bstep (se 2 (by rfl) ⟨652740, by rfl⟩ : syracuseStep 1740641 = 1305481) B1305481
theorem B6590321 : Blo 1156638 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B8359793 : Blo 1156638 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B1740659 : Blo 1156638 1740659 := bstep (se 1 (by rfl) ⟨1305494, by rfl⟩ : syracuseStep 1740659 = 2610989) B2610989
theorem B1740689 : Blo 1156638 1740689 := bstep (se 2 (by rfl) ⟨652758, by rfl⟩ : syracuseStep 1740689 = 1305517) B1305517
theorem B1740707 : Blo 1156638 1740707 := bstep (se 1 (by rfl) ⟨1305530, by rfl⟩ : syracuseStep 1740707 = 2611061) B2611061
theorem B1740737 : Blo 1156638 1740737 := bstep (se 2 (by rfl) ⟨652776, by rfl⟩ : syracuseStep 1740737 = 1305553) B1305553
theorem B1740755 : Blo 1156638 1740755 := bstep (se 1 (by rfl) ⟨1305566, by rfl⟩ : syracuseStep 1740755 = 2611133) B2611133
theorem B1740785 : Blo 1156638 1740785 := bstep (se 2 (by rfl) ⟨652794, by rfl⟩ : syracuseStep 1740785 = 1305589) B1305589
theorem B1740803 : Blo 1156638 1740803 := bstep (se 1 (by rfl) ⟨1305602, by rfl⟩ : syracuseStep 1740803 = 2611205) B2611205
theorem B1740833 : Blo 1156638 1740833 := bstep (se 2 (by rfl) ⟨652812, by rfl⟩ : syracuseStep 1740833 = 1305625) B1305625
theorem B1740851 : Blo 1156638 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B1740881 : Blo 1156638 1740881 := bstep (se 2 (by rfl) ⟨652830, by rfl⟩ : syracuseStep 1740881 = 1305661) B1305661
theorem B1740899 : Blo 1156638 1740899 := bstep (se 1 (by rfl) ⟨1305674, by rfl⟩ : syracuseStep 1740899 = 2611349) B2611349
theorem B1740929 : Blo 1156638 1740929 := bstep (se 2 (by rfl) ⟨652848, by rfl⟩ : syracuseStep 1740929 = 1305697) B1305697
theorem B1740947 : Blo 1156638 1740947 := bstep (se 1 (by rfl) ⟨1305710, by rfl⟩ : syracuseStep 1740947 = 2611421) B2611421
theorem B5869745 : Blo 1156638 5869745 := bstep (se 2 (by rfl) ⟨2201154, by rfl⟩ : syracuseStep 5869745 = 4402309) B4402309
theorem B2199811 : Blo 1156638 2199811 := bstep (se 1 (by rfl) ⟨1649858, by rfl⟩ : syracuseStep 2199811 = 3299717) B3299717
theorem B3707171 : Blo 1156638 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B3903821 : Blo 1156638 3903821 := bstep (se 3 (by rfl) ⟨731966, by rfl⟩ : syracuseStep 3903821 = 1463933) B1463933
theorem B3903875 : Blo 1156638 3903875 := bstep (se 1 (by rfl) ⟨2927906, by rfl⟩ : syracuseStep 3903875 = 5855813) B5855813
theorem B4231565 : Blo 1156638 4231565 := bstep (se 3 (by rfl) ⟨793418, by rfl⟩ : syracuseStep 4231565 = 1586837) B1586837
theorem B3707299 : Blo 1156638 3707299 := bstep (se 1 (by rfl) ⟨2780474, by rfl⟩ : syracuseStep 3707299 = 5560949) B5560949
theorem B4395491 : Blo 1156638 4395491 := bstep (se 1 (by rfl) ⟨3296618, by rfl⟩ : syracuseStep 4395491 = 6593237) B6593237
theorem B4395505 : Blo 1156638 4395505 := bstep (se 2 (by rfl) ⟨1648314, by rfl⟩ : syracuseStep 4395505 = 3296629) B3296629
theorem B30511669 : Blo 1156638 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B15864461 : Blo 1156638 15864461 := bstep (se 3 (by rfl) ⟨2974586, by rfl⟩ : syracuseStep 15864461 = 5949173) B5949173
theorem B3904145 : Blo 1156638 3904145 := bstep (se 2 (by rfl) ⟨1464054, by rfl⟩ : syracuseStep 3904145 = 2928109) B2928109
theorem B2200259 : Blo 1156638 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B3707633 : Blo 1156638 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B2200547 : Blo 1156638 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B3904685 : Blo 1156638 3904685 := bstep (se 3 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 3904685 = 1464257) B1464257
theorem B3904739 : Blo 1156638 3904739 := bstep (se 1 (by rfl) ⟨2928554, by rfl⟩ : syracuseStep 3904739 = 5857109) B5857109
theorem B6591779 : Blo 1156638 6591779 := bstep (se 1 (by rfl) ⟨4943834, by rfl⟩ : syracuseStep 6591779 = 9887669) B9887669
theorem B3905009 : Blo 1156638 3905009 := bstep (se 2 (by rfl) ⟨1464378, by rfl⟩ : syracuseStep 3905009 = 2928757) B2928757
theorem B5871203 : Blo 1156638 5871203 := bstep (se 1 (by rfl) ⟨4403402, by rfl⟩ : syracuseStep 5871203 = 8806805) B8806805
theorem B5281571 : Blo 1156638 5281571 := bstep (se 1 (by rfl) ⟨3961178, by rfl⟩ : syracuseStep 5281571 = 7922357) B7922357
theorem B2201489 : Blo 1156638 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B4396963 : Blo 1156638 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B3905549 : Blo 1156638 3905549 := bstep (se 3 (by rfl) ⟨732290, by rfl⟩ : syracuseStep 3905549 = 1464581) B1464581
theorem B3905603 : Blo 1156638 3905603 := bstep (se 1 (by rfl) ⟨2929202, by rfl⟩ : syracuseStep 3905603 = 5858405) B5858405
theorem B16718021 : Blo 1156638 16718021 := bstep (se 4 (by rfl) ⟨1567314, by rfl⟩ : syracuseStep 16718021 = 3134629) B3134629
theorem B1906931 : Blo 1156638 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B4954445 : Blo 1156638 4954445 := bstep (se 3 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 4954445 = 1857917) B1857917
theorem B3905873 : Blo 1156638 3905873 := bstep (se 2 (by rfl) ⟨1464702, by rfl⟩ : syracuseStep 3905873 = 2929405) B2929405
theorem B8788337 : Blo 1156638 8788337 := bstep (se 2 (by rfl) ⟨3295626, by rfl⟩ : syracuseStep 8788337 = 6591253) B6591253
theorem B5872013 : Blo 1156638 5872013 := bstep (se 3 (by rfl) ⟨1101002, by rfl⟩ : syracuseStep 5872013 = 2202005) B2202005
theorem B2005619 : Blo 1156638 2005619 := bstep (se 1 (by rfl) ⟨1504214, by rfl⟩ : syracuseStep 2005619 = 3008429) B3008429
theorem B2202385 : Blo 1156638 2202385 := bstep (se 2 (by rfl) ⟨825894, by rfl⟩ : syracuseStep 2202385 = 1651789) B1651789
theorem B3906413 : Blo 1156638 3906413 := bstep (se 3 (by rfl) ⟨732452, by rfl⟩ : syracuseStep 3906413 = 1464905) B1464905
theorem B3906467 : Blo 1156638 3906467 := bstep (se 1 (by rfl) ⟨2929850, by rfl⟩ : syracuseStep 3906467 = 5859701) B5859701
theorem B2202545 : Blo 1156638 2202545 := bstep (se 2 (by rfl) ⟨825954, by rfl⟩ : syracuseStep 2202545 = 1651909) B1651909
theorem B6593669 : Blo 1156638 6593669 := bstep (se 4 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 6593669 = 1236313) B1236313
theorem B4168867 : Blo 1156638 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B3906737 : Blo 1156638 3906737 := bstep (se 2 (by rfl) ⟨1465026, by rfl⟩ : syracuseStep 3906737 = 2930053) B2930053
theorem B12524813 : Blo 1156638 12524813 := bstep (se 3 (by rfl) ⟨2348402, by rfl⟩ : syracuseStep 12524813 = 4696805) B4696805
theorem B2202947 : Blo 1156638 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B2006579 : Blo 1156638 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B12525155 : Blo 1156638 12525155 := bstep (se 1 (by rfl) ⟨9393866, by rfl⟩ : syracuseStep 12525155 = 18787733) B18787733
theorem B4169357 : Blo 1156638 4169357 := bstep (se 3 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 4169357 = 1563509) B1563509
theorem B3710605 : Blo 1156638 3710605 := bstep (se 3 (by rfl) ⟨695738, by rfl⟩ : syracuseStep 3710605 = 1391477) B1391477
theorem B12689077 : Blo 1156638 12689077 := bstep (se 5 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 12689077 = 1189601) B1189601
theorem B3907277 : Blo 1156638 3907277 := bstep (se 3 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 3907277 = 1465229) B1465229
theorem B3907331 : Blo 1156638 3907331 := bstep (se 1 (by rfl) ⟨2930498, by rfl⟩ : syracuseStep 3907331 = 5860997) B5860997
theorem B3710861 : Blo 1156638 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B3907601 : Blo 1156638 3907601 := bstep (se 2 (by rfl) ⟨1465350, by rfl⟩ : syracuseStep 3907601 = 2930701) B2930701
theorem B4399181 : Blo 1156638 4399181 := bstep (se 3 (by rfl) ⟨824846, by rfl⟩ : syracuseStep 4399181 = 1649693) B1649693
theorem B6267077 : Blo 1156638 6267077 := bstep (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) B1175077
theorem B5022179 : Blo 1156638 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3908141 : Blo 1156638 3908141 := bstep (se 3 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 3908141 = 1465553) B1465553
theorem B22290997 : Blo 1156638 22290997 := bstep (se 5 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 22290997 = 2089781) B2089781
theorem B3908195 : Blo 1156638 3908195 := bstep (se 1 (by rfl) ⟨2931146, by rfl⟩ : syracuseStep 3908195 = 5862293) B5862293
theorem B3908465 : Blo 1156638 3908465 := bstep (se 2 (by rfl) ⟨1465674, by rfl⟩ : syracuseStep 3908465 = 2931349) B2931349
theorem B1811395 : Blo 1156638 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B9905165 : Blo 1156638 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B5874929 : Blo 1156638 5874929 := bstep (se 2 (by rfl) ⟨2203098, by rfl⟩ : syracuseStep 5874929 = 4406197) B4406197
theorem B1647859 : Blo 1156638 1647859 := bstep (se 1 (by rfl) ⟨1235894, by rfl⟩ : syracuseStep 1647859 = 2471789) B2471789
theorem B3712387 : Blo 1156638 3712387 := bstep (se 1 (by rfl) ⟨2784290, by rfl⟩ : syracuseStep 3712387 = 5568581) B5568581
theorem B3909005 : Blo 1156638 3909005 := bstep (se 3 (by rfl) ⟨732938, by rfl⟩ : syracuseStep 3909005 = 1465877) B1465877
theorem B3909059 : Blo 1156638 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B1156643 : Blo 1156638 1156643 := bstep (se 1 (by rfl) ⟨867482, by rfl⟩ : syracuseStep 1156643 = 1734965) B1734965
theorem B1156659 : Blo 1156638 1156659 := bstep (se 1 (by rfl) ⟨867494, by rfl⟩ : syracuseStep 1156659 = 1734989) B1734989
theorem B1156675 : Blo 1156638 1156675 := bstep (se 1 (by rfl) ⟨867506, by rfl⟩ : syracuseStep 1156675 = 1735013) B1735013
theorem B1156691 : Blo 1156638 1156691 := bstep (se 1 (by rfl) ⟨867518, by rfl⟩ : syracuseStep 1156691 = 1735037) B1735037
theorem B1156707 : Blo 1156638 1156707 := bstep (se 1 (by rfl) ⟨867530, by rfl⟩ : syracuseStep 1156707 = 1735061) B1735061
theorem B1156723 : Blo 1156638 1156723 := bstep (se 1 (by rfl) ⟨867542, by rfl⟩ : syracuseStep 1156723 = 1735085) B1735085
theorem B1156739 : Blo 1156638 1156739 := bstep (se 1 (by rfl) ⟨867554, by rfl⟩ : syracuseStep 1156739 = 1735109) B1735109
theorem B1156755 : Blo 1156638 1156755 := bstep (se 1 (by rfl) ⟨867566, by rfl⟩ : syracuseStep 1156755 = 1735133) B1735133
theorem B1156771 : Blo 1156638 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B1156787 : Blo 1156638 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B1156803 : Blo 1156638 1156803 := bstep (se 1 (by rfl) ⟨867602, by rfl⟩ : syracuseStep 1156803 = 1735205) B1735205
theorem B3909329 : Blo 1156638 3909329 := bstep (se 2 (by rfl) ⟨1465998, by rfl⟩ : syracuseStep 3909329 = 2931997) B2931997
theorem B1156819 : Blo 1156638 1156819 := bstep (se 1 (by rfl) ⟨867614, by rfl⟩ : syracuseStep 1156819 = 1735229) B1735229
theorem B1156835 : Blo 1156638 1156835 := bstep (se 1 (by rfl) ⟨867626, by rfl⟩ : syracuseStep 1156835 = 1735253) B1735253
theorem B1156851 : Blo 1156638 1156851 := bstep (se 1 (by rfl) ⟨867638, by rfl⟩ : syracuseStep 1156851 = 1735277) B1735277
theorem B1156867 : Blo 1156638 1156867 := bstep (se 1 (by rfl) ⟨867650, by rfl⟩ : syracuseStep 1156867 = 1735301) B1735301
theorem B1156883 : Blo 1156638 1156883 := bstep (se 1 (by rfl) ⟨867662, by rfl⟩ : syracuseStep 1156883 = 1735325) B1735325
theorem B25011989 : Blo 1156638 25011989 := bstep (se 6 (by rfl) ⟨586218, by rfl⟩ : syracuseStep 25011989 = 1172437) B1172437
theorem B1156899 : Blo 1156638 1156899 := bstep (se 1 (by rfl) ⟨867674, by rfl⟩ : syracuseStep 1156899 = 1735349) B1735349
theorem B1156915 : Blo 1156638 1156915 := bstep (se 1 (by rfl) ⟨867686, by rfl⟩ : syracuseStep 1156915 = 1735373) B1735373
theorem B1156931 : Blo 1156638 1156931 := bstep (se 1 (by rfl) ⟨867698, by rfl⟩ : syracuseStep 1156931 = 1735397) B1735397
theorem B1156947 : Blo 1156638 1156947 := bstep (se 1 (by rfl) ⟨867710, by rfl⟩ : syracuseStep 1156947 = 1735421) B1735421
theorem B1156963 : Blo 1156638 1156963 := bstep (se 1 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 1156963 = 1735445) B1735445
theorem B3385187 : Blo 1156638 3385187 := bstep (se 1 (by rfl) ⟨2538890, by rfl⟩ : syracuseStep 3385187 = 5077781) B5077781
theorem B7055203 : Blo 1156638 7055203 := bstep (se 1 (by rfl) ⟨5291402, by rfl⟩ : syracuseStep 7055203 = 10582805) B10582805
theorem B1156979 : Blo 1156638 1156979 := bstep (se 1 (by rfl) ⟨867734, by rfl⟩ : syracuseStep 1156979 = 1735469) B1735469
theorem B1156995 : Blo 1156638 1156995 := bstep (se 1 (by rfl) ⟨867746, by rfl⟩ : syracuseStep 1156995 = 1735493) B1735493
theorem B1157011 : Blo 1156638 1157011 := bstep (se 1 (by rfl) ⟨867758, by rfl⟩ : syracuseStep 1157011 = 1735517) B1735517
theorem B1157027 : Blo 1156638 1157027 := bstep (se 1 (by rfl) ⟨867770, by rfl⟩ : syracuseStep 1157027 = 1735541) B1735541
theorem B1157043 : Blo 1156638 1157043 := bstep (se 1 (by rfl) ⟨867782, by rfl⟩ : syracuseStep 1157043 = 1735565) B1735565
theorem B1157059 : Blo 1156638 1157059 := bstep (se 1 (by rfl) ⟨867794, by rfl⟩ : syracuseStep 1157059 = 1735589) B1735589
theorem B1157075 : Blo 1156638 1157075 := bstep (se 1 (by rfl) ⟨867806, by rfl⟩ : syracuseStep 1157075 = 1735613) B1735613
theorem B1157091 : Blo 1156638 1157091 := bstep (se 1 (by rfl) ⟨867818, by rfl⟩ : syracuseStep 1157091 = 1735637) B1735637
theorem B1157107 : Blo 1156638 1157107 := bstep (se 1 (by rfl) ⟨867830, by rfl⟩ : syracuseStep 1157107 = 1735661) B1735661
theorem B1157123 : Blo 1156638 1157123 := bstep (se 1 (by rfl) ⟨867842, by rfl⟩ : syracuseStep 1157123 = 1735685) B1735685
theorem B1157139 : Blo 1156638 1157139 := bstep (se 1 (by rfl) ⟨867854, by rfl⟩ : syracuseStep 1157139 = 1735709) B1735709
theorem B1157155 : Blo 1156638 1157155 := bstep (se 1 (by rfl) ⟨867866, by rfl⟩ : syracuseStep 1157155 = 1735733) B1735733
theorem B1157171 : Blo 1156638 1157171 := bstep (se 1 (by rfl) ⟨867878, by rfl⟩ : syracuseStep 1157171 = 1735757) B1735757
theorem B1157187 : Blo 1156638 1157187 := bstep (se 1 (by rfl) ⟨867890, by rfl⟩ : syracuseStep 1157187 = 1735781) B1735781
theorem B1157203 : Blo 1156638 1157203 := bstep (se 1 (by rfl) ⟨867902, by rfl⟩ : syracuseStep 1157203 = 1735805) B1735805
theorem B2009171 : Blo 1156638 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B1157219 : Blo 1156638 1157219 := bstep (se 1 (by rfl) ⟨867914, by rfl⟩ : syracuseStep 1157219 = 1735829) B1735829
theorem B1157235 : Blo 1156638 1157235 := bstep (se 1 (by rfl) ⟨867926, by rfl⟩ : syracuseStep 1157235 = 1735853) B1735853
theorem B1157251 : Blo 1156638 1157251 := bstep (se 1 (by rfl) ⟨867938, by rfl⟩ : syracuseStep 1157251 = 1735877) B1735877
theorem B1157267 : Blo 1156638 1157267 := bstep (se 1 (by rfl) ⟨867950, by rfl⟩ : syracuseStep 1157267 = 1735901) B1735901
theorem B1157283 : Blo 1156638 1157283 := bstep (se 1 (by rfl) ⟨867962, by rfl⟩ : syracuseStep 1157283 = 1735925) B1735925
theorem B1157299 : Blo 1156638 1157299 := bstep (se 1 (by rfl) ⟨867974, by rfl⟩ : syracuseStep 1157299 = 1735949) B1735949
theorem B1157315 : Blo 1156638 1157315 := bstep (se 1 (by rfl) ⟨867986, by rfl⟩ : syracuseStep 1157315 = 1735973) B1735973
theorem B3713219 : Blo 1156638 3713219 := bstep (se 1 (by rfl) ⟨2784914, by rfl⟩ : syracuseStep 3713219 = 5569829) B5569829
theorem B1157331 : Blo 1156638 1157331 := bstep (se 1 (by rfl) ⟨867998, by rfl⟩ : syracuseStep 1157331 = 1735997) B1735997
theorem B1157347 : Blo 1156638 1157347 := bstep (se 1 (by rfl) ⟨868010, by rfl⟩ : syracuseStep 1157347 = 1736021) B1736021
theorem B7416035 : Blo 1156638 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B3909869 : Blo 1156638 3909869 := bstep (se 3 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 3909869 = 1466201) B1466201
theorem B1157363 : Blo 1156638 1157363 := bstep (se 1 (by rfl) ⟨868022, by rfl⟩ : syracuseStep 1157363 = 1736045) B1736045
theorem B1157379 : Blo 1156638 1157379 := bstep (se 1 (by rfl) ⟨868034, by rfl⟩ : syracuseStep 1157379 = 1736069) B1736069
theorem B1321219 : Blo 1156638 1321219 := bstep (se 1 (by rfl) ⟨990914, by rfl⟩ : syracuseStep 1321219 = 1981829) B1981829
theorem B1157395 : Blo 1156638 1157395 := bstep (se 1 (by rfl) ⟨868046, by rfl⟩ : syracuseStep 1157395 = 1736093) B1736093
theorem B1157411 : Blo 1156638 1157411 := bstep (se 1 (by rfl) ⟨868058, by rfl⟩ : syracuseStep 1157411 = 1736117) B1736117
theorem B3909923 : Blo 1156638 3909923 := bstep (se 1 (by rfl) ⟨2932442, by rfl⟩ : syracuseStep 3909923 = 5864885) B5864885
theorem B1157427 : Blo 1156638 1157427 := bstep (se 1 (by rfl) ⟨868070, by rfl⟩ : syracuseStep 1157427 = 1736141) B1736141
theorem B1157443 : Blo 1156638 1157443 := bstep (se 1 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 1157443 = 1736165) B1736165
theorem B1157459 : Blo 1156638 1157459 := bstep (se 1 (by rfl) ⟨868094, by rfl⟩ : syracuseStep 1157459 = 1736189) B1736189
theorem B1648993 : Blo 1156638 1648993 := bstep (se 2 (by rfl) ⟨618372, by rfl⟩ : syracuseStep 1648993 = 1236745) B1236745
theorem B1157475 : Blo 1156638 1157475 := bstep (se 1 (by rfl) ⟨868106, by rfl⟩ : syracuseStep 1157475 = 1736213) B1736213
theorem B5581169 : Blo 1156638 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B1157491 : Blo 1156638 1157491 := bstep (se 1 (by rfl) ⟨868118, by rfl⟩ : syracuseStep 1157491 = 1736237) B1736237
theorem B1878401 : Blo 1156638 1878401 := bstep (se 2 (by rfl) ⟨704400, by rfl⟩ : syracuseStep 1878401 = 1408801) B1408801
theorem B1157507 : Blo 1156638 1157507 := bstep (se 1 (by rfl) ⟨868130, by rfl⟩ : syracuseStep 1157507 = 1736261) B1736261
theorem B1157523 : Blo 1156638 1157523 := bstep (se 1 (by rfl) ⟨868142, by rfl⟩ : syracuseStep 1157523 = 1736285) B1736285
theorem B1157539 : Blo 1156638 1157539 := bstep (se 1 (by rfl) ⟨868154, by rfl⟩ : syracuseStep 1157539 = 1736309) B1736309
theorem B1157555 : Blo 1156638 1157555 := bstep (se 1 (by rfl) ⟨868166, by rfl⟩ : syracuseStep 1157555 = 1736333) B1736333
theorem B1649089 : Blo 1156638 1649089 := bstep (se 2 (by rfl) ⟨618408, by rfl⟩ : syracuseStep 1649089 = 1236817) B1236817
theorem B1157571 : Blo 1156638 1157571 := bstep (se 1 (by rfl) ⟨868178, by rfl⟩ : syracuseStep 1157571 = 1736357) B1736357
theorem B1157587 : Blo 1156638 1157587 := bstep (se 1 (by rfl) ⟨868190, by rfl⟩ : syracuseStep 1157587 = 1736381) B1736381
theorem B1157603 : Blo 1156638 1157603 := bstep (se 1 (by rfl) ⟨868202, by rfl⟩ : syracuseStep 1157603 = 1736405) B1736405
theorem B1157619 : Blo 1156638 1157619 := bstep (se 1 (by rfl) ⟨868214, by rfl⟩ : syracuseStep 1157619 = 1736429) B1736429
theorem B1157635 : Blo 1156638 1157635 := bstep (se 1 (by rfl) ⟨868226, by rfl⟩ : syracuseStep 1157635 = 1736453) B1736453
theorem B1157651 : Blo 1156638 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B1157667 : Blo 1156638 1157667 := bstep (se 1 (by rfl) ⟨868250, by rfl⟩ : syracuseStep 1157667 = 1736501) B1736501
theorem B3910193 : Blo 1156638 3910193 := bstep (se 2 (by rfl) ⟨1466322, by rfl⟩ : syracuseStep 3910193 = 2932645) B2932645
theorem B1157683 : Blo 1156638 1157683 := bstep (se 1 (by rfl) ⟨868262, by rfl⟩ : syracuseStep 1157683 = 1736525) B1736525
theorem B1157699 : Blo 1156638 1157699 := bstep (se 1 (by rfl) ⟨868274, by rfl⟩ : syracuseStep 1157699 = 1736549) B1736549
theorem B3713617 : Blo 1156638 3713617 := bstep (se 2 (by rfl) ⟨1392606, by rfl⟩ : syracuseStep 3713617 = 2785213) B2785213
theorem B1157715 : Blo 1156638 1157715 := bstep (se 1 (by rfl) ⟨868286, by rfl⟩ : syracuseStep 1157715 = 1736573) B1736573
theorem B1157731 : Blo 1156638 1157731 := bstep (se 1 (by rfl) ⟨868298, by rfl⟩ : syracuseStep 1157731 = 1736597) B1736597
theorem B1157747 : Blo 1156638 1157747 := bstep (se 1 (by rfl) ⟨868310, by rfl⟩ : syracuseStep 1157747 = 1736621) B1736621
theorem B1157763 : Blo 1156638 1157763 := bstep (se 1 (by rfl) ⟨868322, by rfl⟩ : syracuseStep 1157763 = 1736645) B1736645
theorem B3713681 : Blo 1156638 3713681 := bstep (se 2 (by rfl) ⟨1392630, by rfl⟩ : syracuseStep 3713681 = 2785261) B2785261
theorem B1157779 : Blo 1156638 1157779 := bstep (se 1 (by rfl) ⟨868334, by rfl⟩ : syracuseStep 1157779 = 1736669) B1736669
theorem B1157795 : Blo 1156638 1157795 := bstep (se 1 (by rfl) ⟨868346, by rfl⟩ : syracuseStep 1157795 = 1736693) B1736693
theorem B1157811 : Blo 1156638 1157811 := bstep (se 1 (by rfl) ⟨868358, by rfl⟩ : syracuseStep 1157811 = 1736717) B1736717
theorem B1157827 : Blo 1156638 1157827 := bstep (se 1 (by rfl) ⟨868370, by rfl⟩ : syracuseStep 1157827 = 1736741) B1736741
theorem B1157843 : Blo 1156638 1157843 := bstep (se 1 (by rfl) ⟨868382, by rfl⟩ : syracuseStep 1157843 = 1736765) B1736765
theorem B1157859 : Blo 1156638 1157859 := bstep (se 1 (by rfl) ⟨868394, by rfl⟩ : syracuseStep 1157859 = 1736789) B1736789
theorem B1157875 : Blo 1156638 1157875 := bstep (se 1 (by rfl) ⟨868406, by rfl⟩ : syracuseStep 1157875 = 1736813) B1736813
theorem B1157891 : Blo 1156638 1157891 := bstep (se 1 (by rfl) ⟨868418, by rfl⟩ : syracuseStep 1157891 = 1736837) B1736837
theorem B1157907 : Blo 1156638 1157907 := bstep (se 1 (by rfl) ⟨868430, by rfl⟩ : syracuseStep 1157907 = 1736861) B1736861
theorem B1157923 : Blo 1156638 1157923 := bstep (se 1 (by rfl) ⟨868442, by rfl⟩ : syracuseStep 1157923 = 1736885) B1736885
theorem B1157939 : Blo 1156638 1157939 := bstep (se 1 (by rfl) ⟨868454, by rfl⟩ : syracuseStep 1157939 = 1736909) B1736909
theorem B1157955 : Blo 1156638 1157955 := bstep (se 1 (by rfl) ⟨868466, by rfl⟩ : syracuseStep 1157955 = 1736933) B1736933
theorem B1157971 : Blo 1156638 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B1157987 : Blo 1156638 1157987 := bstep (se 1 (by rfl) ⟨868490, by rfl⟩ : syracuseStep 1157987 = 1736981) B1736981
theorem B1158003 : Blo 1156638 1158003 := bstep (se 1 (by rfl) ⟨868502, by rfl⟩ : syracuseStep 1158003 = 1737005) B1737005
theorem B1158019 : Blo 1156638 1158019 := bstep (se 1 (by rfl) ⟨868514, by rfl⟩ : syracuseStep 1158019 = 1737029) B1737029
theorem B1158035 : Blo 1156638 1158035 := bstep (se 1 (by rfl) ⟨868526, by rfl⟩ : syracuseStep 1158035 = 1737053) B1737053
theorem B1158051 : Blo 1156638 1158051 := bstep (se 1 (by rfl) ⟨868538, by rfl⟩ : syracuseStep 1158051 = 1737077) B1737077
theorem B1649585 : Blo 1156638 1649585 := bstep (se 2 (by rfl) ⟨618594, by rfl⟩ : syracuseStep 1649585 = 1237189) B1237189
theorem B4402097 : Blo 1156638 4402097 := bstep (se 2 (by rfl) ⟨1650786, by rfl⟩ : syracuseStep 4402097 = 3301573) B3301573
theorem B1158067 : Blo 1156638 1158067 := bstep (se 1 (by rfl) ⟨868550, by rfl⟩ : syracuseStep 1158067 = 1737101) B1737101
theorem B1158083 : Blo 1156638 1158083 := bstep (se 1 (by rfl) ⟨868562, by rfl⟩ : syracuseStep 1158083 = 1737125) B1737125
theorem B1158099 : Blo 1156638 1158099 := bstep (se 1 (by rfl) ⟨868574, by rfl⟩ : syracuseStep 1158099 = 1737149) B1737149
theorem B1321939 : Blo 1156638 1321939 := bstep (se 1 (by rfl) ⟨991454, by rfl⟩ : syracuseStep 1321939 = 1982909) B1982909
theorem B1158115 : Blo 1156638 1158115 := bstep (se 1 (by rfl) ⟨868586, by rfl⟩ : syracuseStep 1158115 = 1737173) B1737173
theorem B1158131 : Blo 1156638 1158131 := bstep (se 1 (by rfl) ⟨868598, by rfl⟩ : syracuseStep 1158131 = 1737197) B1737197
theorem B1158147 : Blo 1156638 1158147 := bstep (se 1 (by rfl) ⟨868610, by rfl⟩ : syracuseStep 1158147 = 1737221) B1737221
theorem B1158163 : Blo 1156638 1158163 := bstep (se 1 (by rfl) ⟨868622, by rfl⟩ : syracuseStep 1158163 = 1737245) B1737245
theorem B1158179 : Blo 1156638 1158179 := bstep (se 1 (by rfl) ⟨868634, by rfl⟩ : syracuseStep 1158179 = 1737269) B1737269
theorem B1158195 : Blo 1156638 1158195 := bstep (se 1 (by rfl) ⟨868646, by rfl⟩ : syracuseStep 1158195 = 1737293) B1737293
theorem B1158211 : Blo 1156638 1158211 := bstep (se 1 (by rfl) ⟨868658, by rfl⟩ : syracuseStep 1158211 = 1737317) B1737317
theorem B3910733 : Blo 1156638 3910733 := bstep (se 3 (by rfl) ⟨733262, by rfl⟩ : syracuseStep 3910733 = 1466525) B1466525
theorem B1158227 : Blo 1156638 1158227 := bstep (se 1 (by rfl) ⟨868670, by rfl⟩ : syracuseStep 1158227 = 1737341) B1737341
theorem B1158243 : Blo 1156638 1158243 := bstep (se 1 (by rfl) ⟨868682, by rfl⟩ : syracuseStep 1158243 = 1737365) B1737365
theorem B1158259 : Blo 1156638 1158259 := bstep (se 1 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 1158259 = 1737389) B1737389
theorem B1158275 : Blo 1156638 1158275 := bstep (se 1 (by rfl) ⟨868706, by rfl⟩ : syracuseStep 1158275 = 1737413) B1737413
theorem B3910787 : Blo 1156638 3910787 := bstep (se 1 (by rfl) ⟨2933090, by rfl⟩ : syracuseStep 3910787 = 5866181) B5866181
theorem B1158291 : Blo 1156638 1158291 := bstep (se 1 (by rfl) ⟨868718, by rfl⟩ : syracuseStep 1158291 = 1737437) B1737437
theorem B1158307 : Blo 1156638 1158307 := bstep (se 1 (by rfl) ⟨868730, by rfl⟩ : syracuseStep 1158307 = 1737461) B1737461
theorem B1158323 : Blo 1156638 1158323 := bstep (se 1 (by rfl) ⟨868742, by rfl⟩ : syracuseStep 1158323 = 1737485) B1737485
theorem B1158339 : Blo 1156638 1158339 := bstep (se 1 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 1158339 = 1737509) B1737509
theorem B1158355 : Blo 1156638 1158355 := bstep (se 1 (by rfl) ⟨868766, by rfl⟩ : syracuseStep 1158355 = 1737533) B1737533
theorem B1158371 : Blo 1156638 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B1158387 : Blo 1156638 1158387 := bstep (se 1 (by rfl) ⟨868790, by rfl⟩ : syracuseStep 1158387 = 1737581) B1737581
theorem B1158403 : Blo 1156638 1158403 := bstep (se 1 (by rfl) ⟨868802, by rfl⟩ : syracuseStep 1158403 = 1737605) B1737605
theorem B1158419 : Blo 1156638 1158419 := bstep (se 1 (by rfl) ⟨868814, by rfl⟩ : syracuseStep 1158419 = 1737629) B1737629
theorem B1158435 : Blo 1156638 1158435 := bstep (se 1 (by rfl) ⟨868826, by rfl⟩ : syracuseStep 1158435 = 1737653) B1737653
theorem B1158451 : Blo 1156638 1158451 := bstep (se 1 (by rfl) ⟨868838, by rfl⟩ : syracuseStep 1158451 = 1737677) B1737677
theorem B1158467 : Blo 1156638 1158467 := bstep (se 1 (by rfl) ⟨868850, by rfl⟩ : syracuseStep 1158467 = 1737701) B1737701
theorem B1158483 : Blo 1156638 1158483 := bstep (se 1 (by rfl) ⟨868862, by rfl⟩ : syracuseStep 1158483 = 1737725) B1737725
theorem B1158499 : Blo 1156638 1158499 := bstep (se 1 (by rfl) ⟨868874, by rfl⟩ : syracuseStep 1158499 = 1737749) B1737749
theorem B1158515 : Blo 1156638 1158515 := bstep (se 1 (by rfl) ⟨868886, by rfl⟩ : syracuseStep 1158515 = 1737773) B1737773
theorem B1158531 : Blo 1156638 1158531 := bstep (se 1 (by rfl) ⟨868898, by rfl⟩ : syracuseStep 1158531 = 1737797) B1737797
theorem B3911057 : Blo 1156638 3911057 := bstep (se 2 (by rfl) ⟨1466646, by rfl⟩ : syracuseStep 3911057 = 2933293) B2933293
theorem B1158547 : Blo 1156638 1158547 := bstep (se 1 (by rfl) ⟨868910, by rfl⟩ : syracuseStep 1158547 = 1737821) B1737821
theorem B1158563 : Blo 1156638 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B1158579 : Blo 1156638 1158579 := bstep (se 1 (by rfl) ⟨868934, by rfl⟩ : syracuseStep 1158579 = 1737869) B1737869
theorem B1158595 : Blo 1156638 1158595 := bstep (se 1 (by rfl) ⟨868946, by rfl⟩ : syracuseStep 1158595 = 1737893) B1737893
theorem B1158611 : Blo 1156638 1158611 := bstep (se 1 (by rfl) ⟨868958, by rfl⟩ : syracuseStep 1158611 = 1737917) B1737917
theorem B1158627 : Blo 1156638 1158627 := bstep (se 1 (by rfl) ⟨868970, by rfl⟩ : syracuseStep 1158627 = 1737941) B1737941
theorem B1158643 : Blo 1156638 1158643 := bstep (se 1 (by rfl) ⟨868982, by rfl⟩ : syracuseStep 1158643 = 1737965) B1737965
theorem B1158659 : Blo 1156638 1158659 := bstep (se 1 (by rfl) ⟨868994, by rfl⟩ : syracuseStep 1158659 = 1737989) B1737989
theorem B1158675 : Blo 1156638 1158675 := bstep (se 1 (by rfl) ⟨869006, by rfl⟩ : syracuseStep 1158675 = 1738013) B1738013
theorem B1158691 : Blo 1156638 1158691 := bstep (se 1 (by rfl) ⟨869018, by rfl⟩ : syracuseStep 1158691 = 1738037) B1738037
theorem B1158707 : Blo 1156638 1158707 := bstep (se 1 (by rfl) ⟨869030, by rfl⟩ : syracuseStep 1158707 = 1738061) B1738061
theorem B1158723 : Blo 1156638 1158723 := bstep (se 1 (by rfl) ⟨869042, by rfl⟩ : syracuseStep 1158723 = 1738085) B1738085
theorem B1158739 : Blo 1156638 1158739 := bstep (se 1 (by rfl) ⟨869054, by rfl⟩ : syracuseStep 1158739 = 1738109) B1738109
theorem B1158755 : Blo 1156638 1158755 := bstep (se 1 (by rfl) ⟨869066, by rfl⟩ : syracuseStep 1158755 = 1738133) B1738133
theorem B1158771 : Blo 1156638 1158771 := bstep (se 1 (by rfl) ⟨869078, by rfl⟩ : syracuseStep 1158771 = 1738157) B1738157
theorem B1158787 : Blo 1156638 1158787 := bstep (se 1 (by rfl) ⟨869090, by rfl⟩ : syracuseStep 1158787 = 1738181) B1738181
theorem B1158803 : Blo 1156638 1158803 := bstep (se 1 (by rfl) ⟨869102, by rfl⟩ : syracuseStep 1158803 = 1738205) B1738205
theorem B1158819 : Blo 1156638 1158819 := bstep (se 1 (by rfl) ⟨869114, by rfl⟩ : syracuseStep 1158819 = 1738229) B1738229
theorem B1322659 : Blo 1156638 1322659 := bstep (se 1 (by rfl) ⟨991994, by rfl⟩ : syracuseStep 1322659 = 1983989) B1983989
theorem B1158835 : Blo 1156638 1158835 := bstep (se 1 (by rfl) ⟨869126, by rfl⟩ : syracuseStep 1158835 = 1738253) B1738253
theorem B13184693 : Blo 1156638 13184693 := bstep (se 5 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 13184693 = 1236065) B1236065
theorem B1158851 : Blo 1156638 1158851 := bstep (se 1 (by rfl) ⟨869138, by rfl⟩ : syracuseStep 1158851 = 1738277) B1738277
theorem B1158867 : Blo 1156638 1158867 := bstep (se 1 (by rfl) ⟨869150, by rfl⟩ : syracuseStep 1158867 = 1738301) B1738301
theorem B1158883 : Blo 1156638 1158883 := bstep (se 1 (by rfl) ⟨869162, by rfl⟩ : syracuseStep 1158883 = 1738325) B1738325
theorem B1158899 : Blo 1156638 1158899 := bstep (se 1 (by rfl) ⟨869174, by rfl⟩ : syracuseStep 1158899 = 1738349) B1738349
theorem B1158915 : Blo 1156638 1158915 := bstep (se 1 (by rfl) ⟨869186, by rfl⟩ : syracuseStep 1158915 = 1738373) B1738373
theorem B1158931 : Blo 1156638 1158931 := bstep (se 1 (by rfl) ⟨869198, by rfl⟩ : syracuseStep 1158931 = 1738397) B1738397
theorem B1650451 : Blo 1156638 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B1158947 : Blo 1156638 1158947 := bstep (se 1 (by rfl) ⟨869210, by rfl⟩ : syracuseStep 1158947 = 1738421) B1738421
theorem B2928433 : Blo 1156638 2928433 := bstep (se 2 (by rfl) ⟨1098162, by rfl⟩ : syracuseStep 2928433 = 2196325) B2196325
theorem B1158963 : Blo 1156638 1158963 := bstep (se 1 (by rfl) ⟨869222, by rfl⟩ : syracuseStep 1158963 = 1738445) B1738445
theorem B1158979 : Blo 1156638 1158979 := bstep (se 1 (by rfl) ⟨869234, by rfl⟩ : syracuseStep 1158979 = 1738469) B1738469
theorem B1158995 : Blo 1156638 1158995 := bstep (se 1 (by rfl) ⟨869246, by rfl⟩ : syracuseStep 1158995 = 1738493) B1738493
theorem B1159011 : Blo 1156638 1159011 := bstep (se 1 (by rfl) ⟨869258, by rfl⟩ : syracuseStep 1159011 = 1738517) B1738517
theorem B1159027 : Blo 1156638 1159027 := bstep (se 1 (by rfl) ⟨869270, by rfl⟩ : syracuseStep 1159027 = 1738541) B1738541
theorem B1650547 : Blo 1156638 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1159043 : Blo 1156638 1159043 := bstep (se 1 (by rfl) ⟨869282, by rfl⟩ : syracuseStep 1159043 = 1738565) B1738565
theorem B1159059 : Blo 1156638 1159059 := bstep (se 1 (by rfl) ⟨869294, by rfl⟩ : syracuseStep 1159059 = 1738589) B1738589
theorem B1159075 : Blo 1156638 1159075 := bstep (se 1 (by rfl) ⟨869306, by rfl⟩ : syracuseStep 1159075 = 1738613) B1738613
theorem B3911597 : Blo 1156638 3911597 := bstep (se 3 (by rfl) ⟨733424, by rfl⟩ : syracuseStep 3911597 = 1466849) B1466849
theorem B1159091 : Blo 1156638 1159091 := bstep (se 1 (by rfl) ⟨869318, by rfl⟩ : syracuseStep 1159091 = 1738637) B1738637
theorem B1159107 : Blo 1156638 1159107 := bstep (se 1 (by rfl) ⟨869330, by rfl⟩ : syracuseStep 1159107 = 1738661) B1738661
theorem B1159123 : Blo 1156638 1159123 := bstep (se 1 (by rfl) ⟨869342, by rfl⟩ : syracuseStep 1159123 = 1738685) B1738685
theorem B3911651 : Blo 1156638 3911651 := bstep (se 1 (by rfl) ⟨2933738, by rfl⟩ : syracuseStep 3911651 = 5867477) B5867477
theorem B1159139 : Blo 1156638 1159139 := bstep (se 1 (by rfl) ⟨869354, by rfl⟩ : syracuseStep 1159139 = 1738709) B1738709
theorem B1159155 : Blo 1156638 1159155 := bstep (se 1 (by rfl) ⟨869366, by rfl⟩ : syracuseStep 1159155 = 1738733) B1738733
theorem B1159171 : Blo 1156638 1159171 := bstep (se 1 (by rfl) ⟨869378, by rfl⟩ : syracuseStep 1159171 = 1738757) B1738757
theorem B1159187 : Blo 1156638 1159187 := bstep (se 1 (by rfl) ⟨869390, by rfl⟩ : syracuseStep 1159187 = 1738781) B1738781
theorem B1159203 : Blo 1156638 1159203 := bstep (se 1 (by rfl) ⟨869402, by rfl⟩ : syracuseStep 1159203 = 1738805) B1738805
theorem B1159219 : Blo 1156638 1159219 := bstep (se 1 (by rfl) ⟨869414, by rfl⟩ : syracuseStep 1159219 = 1738829) B1738829
theorem B2928707 : Blo 1156638 2928707 := bstep (se 1 (by rfl) ⟨2196530, by rfl⟩ : syracuseStep 2928707 = 4393061) B4393061
theorem B1159235 : Blo 1156638 1159235 := bstep (se 1 (by rfl) ⟨869426, by rfl⟩ : syracuseStep 1159235 = 1738853) B1738853
theorem B1159251 : Blo 1156638 1159251 := bstep (se 1 (by rfl) ⟨869438, by rfl⟩ : syracuseStep 1159251 = 1738877) B1738877
theorem B1159267 : Blo 1156638 1159267 := bstep (se 1 (by rfl) ⟨869450, by rfl⟩ : syracuseStep 1159267 = 1738901) B1738901
theorem B6697073 : Blo 1156638 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B1159283 : Blo 1156638 1159283 := bstep (se 1 (by rfl) ⟨869462, by rfl⟩ : syracuseStep 1159283 = 1738925) B1738925
theorem B1159299 : Blo 1156638 1159299 := bstep (se 1 (by rfl) ⟨869474, by rfl⟩ : syracuseStep 1159299 = 1738949) B1738949
theorem B1159315 : Blo 1156638 1159315 := bstep (se 1 (by rfl) ⟨869486, by rfl⟩ : syracuseStep 1159315 = 1738973) B1738973
theorem B1159331 : Blo 1156638 1159331 := bstep (se 1 (by rfl) ⟨869498, by rfl⟩ : syracuseStep 1159331 = 1738997) B1738997
theorem B1159347 : Blo 1156638 1159347 := bstep (se 1 (by rfl) ⟨869510, by rfl⟩ : syracuseStep 1159347 = 1739021) B1739021
theorem B1159363 : Blo 1156638 1159363 := bstep (se 1 (by rfl) ⟨869522, by rfl⟩ : syracuseStep 1159363 = 1739045) B1739045
theorem B1159379 : Blo 1156638 1159379 := bstep (se 1 (by rfl) ⟨869534, by rfl⟩ : syracuseStep 1159379 = 1739069) B1739069
theorem B1159395 : Blo 1156638 1159395 := bstep (se 1 (by rfl) ⟨869546, by rfl⟩ : syracuseStep 1159395 = 1739093) B1739093
theorem B3911921 : Blo 1156638 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B1159411 : Blo 1156638 1159411 := bstep (se 1 (by rfl) ⟨869558, by rfl⟩ : syracuseStep 1159411 = 1739117) B1739117
theorem B2928899 : Blo 1156638 2928899 := bstep (se 1 (by rfl) ⟨2196674, by rfl⟩ : syracuseStep 2928899 = 4393349) B4393349
theorem B1159427 : Blo 1156638 1159427 := bstep (se 1 (by rfl) ⟨869570, by rfl⟩ : syracuseStep 1159427 = 1739141) B1739141
theorem B1159443 : Blo 1156638 1159443 := bstep (se 1 (by rfl) ⟨869582, by rfl⟩ : syracuseStep 1159443 = 1739165) B1739165
theorem B1159459 : Blo 1156638 1159459 := bstep (se 1 (by rfl) ⟨869594, by rfl⟩ : syracuseStep 1159459 = 1739189) B1739189
theorem B4174129 : Blo 1156638 4174129 := bstep (se 2 (by rfl) ⟨1565298, by rfl⟩ : syracuseStep 4174129 = 3130597) B3130597
theorem B1159475 : Blo 1156638 1159475 := bstep (se 1 (by rfl) ⟨869606, by rfl⟩ : syracuseStep 1159475 = 1739213) B1739213
theorem B1159491 : Blo 1156638 1159491 := bstep (se 1 (by rfl) ⟨869618, by rfl⟩ : syracuseStep 1159491 = 1739237) B1739237
theorem B1159507 : Blo 1156638 1159507 := bstep (se 1 (by rfl) ⟨869630, by rfl⟩ : syracuseStep 1159507 = 1739261) B1739261
theorem B1159523 : Blo 1156638 1159523 := bstep (se 1 (by rfl) ⟨869642, by rfl⟩ : syracuseStep 1159523 = 1739285) B1739285
theorem B1651043 : Blo 1156638 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B4403555 : Blo 1156638 4403555 := bstep (se 1 (by rfl) ⟨3302666, by rfl⟩ : syracuseStep 4403555 = 6605333) B6605333
theorem B1159539 : Blo 1156638 1159539 := bstep (se 1 (by rfl) ⟨869654, by rfl⟩ : syracuseStep 1159539 = 1739309) B1739309
theorem B1159555 : Blo 1156638 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B1159571 : Blo 1156638 1159571 := bstep (se 1 (by rfl) ⟨869678, by rfl⟩ : syracuseStep 1159571 = 1739357) B1739357
theorem B1159587 : Blo 1156638 1159587 := bstep (se 1 (by rfl) ⟨869690, by rfl⟩ : syracuseStep 1159587 = 1739381) B1739381
theorem B1159603 : Blo 1156638 1159603 := bstep (se 1 (by rfl) ⟨869702, by rfl⟩ : syracuseStep 1159603 = 1739405) B1739405
theorem B1159619 : Blo 1156638 1159619 := bstep (se 1 (by rfl) ⟨869714, by rfl⟩ : syracuseStep 1159619 = 1739429) B1739429
theorem B1159635 : Blo 1156638 1159635 := bstep (se 1 (by rfl) ⟨869726, by rfl⟩ : syracuseStep 1159635 = 1739453) B1739453
theorem B1159651 : Blo 1156638 1159651 := bstep (se 1 (by rfl) ⟨869738, by rfl⟩ : syracuseStep 1159651 = 1739477) B1739477
theorem B1159667 : Blo 1156638 1159667 := bstep (se 1 (by rfl) ⟨869750, by rfl⟩ : syracuseStep 1159667 = 1739501) B1739501
theorem B1159683 : Blo 1156638 1159683 := bstep (se 1 (by rfl) ⟨869762, by rfl⟩ : syracuseStep 1159683 = 1739525) B1739525
theorem B1159699 : Blo 1156638 1159699 := bstep (se 1 (by rfl) ⟨869774, by rfl⟩ : syracuseStep 1159699 = 1739549) B1739549
theorem B1159715 : Blo 1156638 1159715 := bstep (se 1 (by rfl) ⟨869786, by rfl⟩ : syracuseStep 1159715 = 1739573) B1739573
theorem B1159731 : Blo 1156638 1159731 := bstep (se 1 (by rfl) ⟨869798, by rfl⟩ : syracuseStep 1159731 = 1739597) B1739597
theorem B1880641 : Blo 1156638 1880641 := bstep (se 2 (by rfl) ⟨705240, by rfl⟩ : syracuseStep 1880641 = 1410481) B1410481
theorem B1159747 : Blo 1156638 1159747 := bstep (se 1 (by rfl) ⟨869810, by rfl⟩ : syracuseStep 1159747 = 1739621) B1739621
theorem B1159763 : Blo 1156638 1159763 := bstep (se 1 (by rfl) ⟨869822, by rfl⟩ : syracuseStep 1159763 = 1739645) B1739645
theorem B1159779 : Blo 1156638 1159779 := bstep (se 1 (by rfl) ⟨869834, by rfl⟩ : syracuseStep 1159779 = 1739669) B1739669
theorem B1159795 : Blo 1156638 1159795 := bstep (se 1 (by rfl) ⟨869846, by rfl⟩ : syracuseStep 1159795 = 1739693) B1739693
theorem B1159811 : Blo 1156638 1159811 := bstep (se 1 (by rfl) ⟨869858, by rfl⟩ : syracuseStep 1159811 = 1739717) B1739717
theorem B1159827 : Blo 1156638 1159827 := bstep (se 1 (by rfl) ⟨869870, by rfl⟩ : syracuseStep 1159827 = 1739741) B1739741
theorem B1159843 : Blo 1156638 1159843 := bstep (se 1 (by rfl) ⟨869882, by rfl⟩ : syracuseStep 1159843 = 1739765) B1739765
theorem B1159859 : Blo 1156638 1159859 := bstep (se 1 (by rfl) ⟨869894, by rfl⟩ : syracuseStep 1159859 = 1739789) B1739789
theorem B1159875 : Blo 1156638 1159875 := bstep (se 1 (by rfl) ⟨869906, by rfl⟩ : syracuseStep 1159875 = 1739813) B1739813
theorem B1159891 : Blo 1156638 1159891 := bstep (se 1 (by rfl) ⟨869918, by rfl⟩ : syracuseStep 1159891 = 1739837) B1739837
theorem B1159907 : Blo 1156638 1159907 := bstep (se 1 (by rfl) ⟨869930, by rfl⟩ : syracuseStep 1159907 = 1739861) B1739861
theorem B1159923 : Blo 1156638 1159923 := bstep (se 1 (by rfl) ⟨869942, by rfl⟩ : syracuseStep 1159923 = 1739885) B1739885
theorem B1159939 : Blo 1156638 1159939 := bstep (se 1 (by rfl) ⟨869954, by rfl⟩ : syracuseStep 1159939 = 1739909) B1739909
theorem B3912461 : Blo 1156638 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B1159955 : Blo 1156638 1159955 := bstep (se 1 (by rfl) ⟨869966, by rfl⟩ : syracuseStep 1159955 = 1739933) B1739933
theorem B1159971 : Blo 1156638 1159971 := bstep (se 1 (by rfl) ⟨869978, by rfl⟩ : syracuseStep 1159971 = 1739957) B1739957
theorem B1159987 : Blo 1156638 1159987 := bstep (se 1 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 1159987 = 1739981) B1739981
theorem B3912515 : Blo 1156638 3912515 := bstep (se 1 (by rfl) ⟨2934386, by rfl⟩ : syracuseStep 3912515 = 5868773) B5868773
theorem B1160003 : Blo 1156638 1160003 := bstep (se 1 (by rfl) ⟨870002, by rfl⟩ : syracuseStep 1160003 = 1740005) B1740005
theorem B6599501 : Blo 1156638 6599501 := bstep (se 3 (by rfl) ⟨1237406, by rfl⟩ : syracuseStep 6599501 = 2474813) B2474813
theorem B1160019 : Blo 1156638 1160019 := bstep (se 1 (by rfl) ⟨870014, by rfl⟩ : syracuseStep 1160019 = 1740029) B1740029
theorem B1160035 : Blo 1156638 1160035 := bstep (se 1 (by rfl) ⟨870026, by rfl⟩ : syracuseStep 1160035 = 1740053) B1740053
theorem B1160051 : Blo 1156638 1160051 := bstep (se 1 (by rfl) ⟨870038, by rfl⟩ : syracuseStep 1160051 = 1740077) B1740077
theorem B1160067 : Blo 1156638 1160067 := bstep (se 1 (by rfl) ⟨870050, by rfl⟩ : syracuseStep 1160067 = 1740101) B1740101
theorem B53523341 : Blo 1156638 53523341 := bstep (se 3 (by rfl) ⟨10035626, by rfl⟩ : syracuseStep 53523341 = 20071253) B20071253
theorem B1160083 : Blo 1156638 1160083 := bstep (se 1 (by rfl) ⟨870062, by rfl⟩ : syracuseStep 1160083 = 1740125) B1740125
theorem B1160099 : Blo 1156638 1160099 := bstep (se 1 (by rfl) ⟨870074, by rfl⟩ : syracuseStep 1160099 = 1740149) B1740149
theorem B1160115 : Blo 1156638 1160115 := bstep (se 1 (by rfl) ⟨870086, by rfl⟩ : syracuseStep 1160115 = 1740173) B1740173
theorem B1160131 : Blo 1156638 1160131 := bstep (se 1 (by rfl) ⟨870098, by rfl⟩ : syracuseStep 1160131 = 1740197) B1740197
theorem B1160147 : Blo 1156638 1160147 := bstep (se 1 (by rfl) ⟨870110, by rfl⟩ : syracuseStep 1160147 = 1740221) B1740221
theorem B1651681 : Blo 1156638 1651681 := bstep (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) B1238761
theorem B1160163 : Blo 1156638 1160163 := bstep (se 1 (by rfl) ⟨870122, by rfl⟩ : syracuseStep 1160163 = 1740245) B1740245
theorem B1160179 : Blo 1156638 1160179 := bstep (se 1 (by rfl) ⟨870134, by rfl⟩ : syracuseStep 1160179 = 1740269) B1740269
theorem B1586179 : Blo 1156638 1586179 := bstep (se 1 (by rfl) ⟨1189634, by rfl⟩ : syracuseStep 1586179 = 2379269) B2379269
theorem B1160195 : Blo 1156638 1160195 := bstep (se 1 (by rfl) ⟨870146, by rfl⟩ : syracuseStep 1160195 = 1740293) B1740293
theorem B1160211 : Blo 1156638 1160211 := bstep (se 1 (by rfl) ⟨870158, by rfl⟩ : syracuseStep 1160211 = 1740317) B1740317
theorem B1160227 : Blo 1156638 1160227 := bstep (se 1 (by rfl) ⟨870170, by rfl⟩ : syracuseStep 1160227 = 1740341) B1740341
theorem B2470961 : Blo 1156638 2470961 := bstep (se 2 (by rfl) ⟨926610, by rfl⟩ : syracuseStep 2470961 = 1853221) B1853221
theorem B1160243 : Blo 1156638 1160243 := bstep (se 1 (by rfl) ⟨870182, by rfl⟩ : syracuseStep 1160243 = 1740365) B1740365
theorem B1160259 : Blo 1156638 1160259 := bstep (se 1 (by rfl) ⟨870194, by rfl⟩ : syracuseStep 1160259 = 1740389) B1740389
theorem B3912785 : Blo 1156638 3912785 := bstep (se 2 (by rfl) ⟨1467294, by rfl⟩ : syracuseStep 3912785 = 2934589) B2934589
theorem B1160275 : Blo 1156638 1160275 := bstep (se 1 (by rfl) ⟨870206, by rfl⟩ : syracuseStep 1160275 = 1740413) B1740413
theorem B1160291 : Blo 1156638 1160291 := bstep (se 1 (by rfl) ⟨870218, by rfl⟩ : syracuseStep 1160291 = 1740437) B1740437
theorem B1160307 : Blo 1156638 1160307 := bstep (se 1 (by rfl) ⟨870230, by rfl⟩ : syracuseStep 1160307 = 1740461) B1740461
theorem B1160323 : Blo 1156638 1160323 := bstep (se 1 (by rfl) ⟨870242, by rfl⟩ : syracuseStep 1160323 = 1740485) B1740485
theorem B1160339 : Blo 1156638 1160339 := bstep (se 1 (by rfl) ⟨870254, by rfl⟩ : syracuseStep 1160339 = 1740509) B1740509
theorem B1160355 : Blo 1156638 1160355 := bstep (se 1 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 1160355 = 1740533) B1740533
theorem B2929841 : Blo 1156638 2929841 := bstep (se 2 (by rfl) ⟨1098690, by rfl⟩ : syracuseStep 2929841 = 2197381) B2197381
theorem B1160371 : Blo 1156638 1160371 := bstep (se 1 (by rfl) ⟨870278, by rfl⟩ : syracuseStep 1160371 = 1740557) B1740557
theorem B1160387 : Blo 1156638 1160387 := bstep (se 1 (by rfl) ⟨870290, by rfl⟩ : syracuseStep 1160387 = 1740581) B1740581
theorem B1160403 : Blo 1156638 1160403 := bstep (se 1 (by rfl) ⟨870302, by rfl⟩ : syracuseStep 1160403 = 1740605) B1740605
theorem B2929891 : Blo 1156638 2929891 := bstep (se 1 (by rfl) ⟨2197418, by rfl⟩ : syracuseStep 2929891 = 4394837) B4394837
theorem B1160419 : Blo 1156638 1160419 := bstep (se 1 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 1160419 = 1740629) B1740629
theorem B1160435 : Blo 1156638 1160435 := bstep (se 1 (by rfl) ⟨870326, by rfl⟩ : syracuseStep 1160435 = 1740653) B1740653
theorem B1160451 : Blo 1156638 1160451 := bstep (se 1 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 1160451 = 1740677) B1740677
theorem B1160467 : Blo 1156638 1160467 := bstep (se 1 (by rfl) ⟨870350, by rfl⟩ : syracuseStep 1160467 = 1740701) B1740701
theorem B1160483 : Blo 1156638 1160483 := bstep (se 1 (by rfl) ⟨870362, by rfl⟩ : syracuseStep 1160483 = 1740725) B1740725
theorem B1652017 : Blo 1156638 1652017 := bstep (se 2 (by rfl) ⟨619506, by rfl⟩ : syracuseStep 1652017 = 1239013) B1239013
theorem B1160499 : Blo 1156638 1160499 := bstep (se 1 (by rfl) ⟨870374, by rfl⟩ : syracuseStep 1160499 = 1740749) B1740749
theorem B1160515 : Blo 1156638 1160515 := bstep (se 1 (by rfl) ⟨870386, by rfl⟩ : syracuseStep 1160515 = 1740773) B1740773
theorem B4404557 : Blo 1156638 4404557 := bstep (se 3 (by rfl) ⟨825854, by rfl⟩ : syracuseStep 4404557 = 1651709) B1651709
theorem B1160531 : Blo 1156638 1160531 := bstep (se 1 (by rfl) ⟨870398, by rfl⟩ : syracuseStep 1160531 = 1740797) B1740797
theorem B1160547 : Blo 1156638 1160547 := bstep (se 1 (by rfl) ⟨870410, by rfl⟩ : syracuseStep 1160547 = 1740821) B1740821
theorem B2930033 : Blo 1156638 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B1160563 : Blo 1156638 1160563 := bstep (se 1 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 1160563 = 1740845) B1740845
theorem B1160579 : Blo 1156638 1160579 := bstep (se 1 (by rfl) ⟨870434, by rfl⟩ : syracuseStep 1160579 = 1740869) B1740869
theorem B1160595 : Blo 1156638 1160595 := bstep (se 1 (by rfl) ⟨870446, by rfl⟩ : syracuseStep 1160595 = 1740893) B1740893
theorem B1160611 : Blo 1156638 1160611 := bstep (se 1 (by rfl) ⟨870458, by rfl⟩ : syracuseStep 1160611 = 1740917) B1740917
theorem B1160627 : Blo 1156638 1160627 := bstep (se 1 (by rfl) ⟨870470, by rfl⟩ : syracuseStep 1160627 = 1740941) B1740941
theorem B3913325 : Blo 1156638 3913325 := bstep (se 3 (by rfl) ⟨733748, by rfl⟩ : syracuseStep 3913325 = 1467497) B1467497
theorem B3913379 : Blo 1156638 3913379 := bstep (se 1 (by rfl) ⟨2935034, by rfl⟩ : syracuseStep 3913379 = 5870069) B5870069
theorem B2602673 : Blo 1156638 2602673 := bstep (se 2 (by rfl) ⟨976002, by rfl⟩ : syracuseStep 2602673 = 1952005) B1952005
theorem B2602691 : Blo 1156638 2602691 := bstep (se 1 (by rfl) ⟨1952018, by rfl⟩ : syracuseStep 2602691 = 3904037) B3904037
theorem B1718083 : Blo 1156638 1718083 := bstep (se 1 (by rfl) ⟨1288562, by rfl⟩ : syracuseStep 1718083 = 2577125) B2577125
theorem B3913649 : Blo 1156638 3913649 := bstep (se 2 (by rfl) ⟨1467618, by rfl⟩ : syracuseStep 3913649 = 2935237) B2935237
theorem B2602961 : Blo 1156638 2602961 := bstep (se 2 (by rfl) ⟨976110, by rfl⟩ : syracuseStep 2602961 = 1952221) B1952221
theorem B2602979 : Blo 1156638 2602979 := bstep (se 1 (by rfl) ⟨1952234, by rfl⟩ : syracuseStep 2602979 = 3904469) B3904469
theorem B2504753 : Blo 1156638 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B35665973 : Blo 1156638 35665973 := bstep (se 5 (by rfl) ⟨1671842, by rfl⟩ : syracuseStep 35665973 = 3343685) B3343685
theorem B7420081 : Blo 1156638 7420081 := bstep (se 2 (by rfl) ⟨2782530, by rfl⟩ : syracuseStep 7420081 = 5565061) B5565061
theorem B4700387 : Blo 1156638 4700387 := bstep (se 1 (by rfl) ⟨3525290, by rfl⟩ : syracuseStep 4700387 = 7050581) B7050581
theorem B2603249 : Blo 1156638 2603249 := bstep (se 2 (by rfl) ⟨976218, by rfl⟩ : syracuseStep 2603249 = 1952437) B1952437
theorem B2603267 : Blo 1156638 2603267 := bstep (se 1 (by rfl) ⟨1952450, by rfl⟩ : syracuseStep 2603267 = 3904901) B3904901
theorem B1390915 : Blo 1156638 1390915 := bstep (se 1 (by rfl) ⟨1043186, by rfl⟩ : syracuseStep 1390915 = 2086373) B2086373
theorem B2931025 : Blo 1156638 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B3914189 : Blo 1156638 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B3521009 : Blo 1156638 3521009 := bstep (se 2 (by rfl) ⟨1320378, by rfl⟩ : syracuseStep 3521009 = 2640757) B2640757
theorem B3258883 : Blo 1156638 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B3914243 : Blo 1156638 3914243 := bstep (se 1 (by rfl) ⟨2935682, by rfl⟩ : syracuseStep 3914243 = 5871365) B5871365
theorem B2603537 : Blo 1156638 2603537 := bstep (se 2 (by rfl) ⟨976326, by rfl⟩ : syracuseStep 2603537 = 1952653) B1952653
theorem B2603555 : Blo 1156638 2603555 := bstep (se 1 (by rfl) ⟨1952666, by rfl⟩ : syracuseStep 2603555 = 3905333) B3905333
theorem B2931299 : Blo 1156638 2931299 := bstep (se 1 (by rfl) ⟨2198474, by rfl⟩ : syracuseStep 2931299 = 4396949) B4396949
theorem B1587811 : Blo 1156638 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B6273649 : Blo 1156638 6273649 := bstep (se 2 (by rfl) ⟨2352618, by rfl⟩ : syracuseStep 6273649 = 4705237) B4705237
theorem B2472643 : Blo 1156638 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B8043235 : Blo 1156638 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B3717859 : Blo 1156638 3717859 := bstep (se 1 (by rfl) ⟨2788394, by rfl⟩ : syracuseStep 3717859 = 5576789) B5576789
theorem B3914513 : Blo 1156638 3914513 := bstep (se 2 (by rfl) ⟨1467942, by rfl⟩ : syracuseStep 3914513 = 2935885) B2935885
theorem B2931491 : Blo 1156638 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B2603825 : Blo 1156638 2603825 := bstep (se 2 (by rfl) ⟨976434, by rfl⟩ : syracuseStep 2603825 = 1952869) B1952869
theorem B2603843 : Blo 1156638 2603843 := bstep (se 1 (by rfl) ⟨1952882, by rfl⟩ : syracuseStep 2603843 = 3905765) B3905765
theorem B6601733 : Blo 1156638 6601733 := bstep (se 4 (by rfl) ⟨618912, by rfl⟩ : syracuseStep 6601733 = 1237825) B1237825
theorem B3128401 : Blo 1156638 3128401 := bstep (se 2 (by rfl) ⟨1173150, by rfl⟩ : syracuseStep 3128401 = 2346301) B2346301
theorem B2604113 : Blo 1156638 2604113 := bstep (se 2 (by rfl) ⟨976542, by rfl⟩ : syracuseStep 2604113 = 1953085) B1953085
theorem B1588307 : Blo 1156638 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B2604131 : Blo 1156638 2604131 := bstep (se 1 (by rfl) ⟨1953098, by rfl⟩ : syracuseStep 2604131 = 3906197) B3906197
theorem B2473105 : Blo 1156638 2473105 := bstep (se 2 (by rfl) ⟨927414, by rfl⟩ : syracuseStep 2473105 = 1854829) B1854829
theorem B1981649 : Blo 1156638 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B3915053 : Blo 1156638 3915053 := bstep (se 3 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 3915053 = 1468145) B1468145
theorem B3915107 : Blo 1156638 3915107 := bstep (se 1 (by rfl) ⟨2936330, by rfl⟩ : syracuseStep 3915107 = 5872661) B5872661
theorem B2604401 : Blo 1156638 2604401 := bstep (se 2 (by rfl) ⟨976650, by rfl⟩ : syracuseStep 2604401 = 1953301) B1953301
theorem B2604419 : Blo 1156638 2604419 := bstep (se 1 (by rfl) ⟨1953314, by rfl⟩ : syracuseStep 2604419 = 3906629) B3906629
theorem B4406669 : Blo 1156638 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B14859845 : Blo 1156638 14859845 := bstep (se 4 (by rfl) ⟨1393110, by rfl⟩ : syracuseStep 14859845 = 2786221) B2786221
theorem B3915377 : Blo 1156638 3915377 := bstep (se 2 (by rfl) ⟨1468266, by rfl⟩ : syracuseStep 3915377 = 2936533) B2936533
theorem B3128963 : Blo 1156638 3128963 := bstep (se 1 (by rfl) ⟨2346722, by rfl⟩ : syracuseStep 3128963 = 4693445) B4693445
theorem B2604689 : Blo 1156638 2604689 := bstep (se 2 (by rfl) ⟨976758, by rfl⟩ : syracuseStep 2604689 = 1953517) B1953517
theorem B2604707 : Blo 1156638 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B7618225 : Blo 1156638 7618225 := bstep (se 2 (by rfl) ⟨2856834, by rfl⟩ : syracuseStep 7618225 = 5713669) B5713669
theorem B6602417 : Blo 1156638 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B2932433 : Blo 1156638 2932433 := bstep (se 2 (by rfl) ⟨1099662, by rfl⟩ : syracuseStep 2932433 = 2199325) B2199325
theorem B2932483 : Blo 1156638 2932483 := bstep (se 1 (by rfl) ⟨2199362, by rfl⟩ : syracuseStep 2932483 = 4398725) B4398725
theorem B2932625 : Blo 1156638 2932625 := bstep (se 2 (by rfl) ⟨1099734, by rfl⟩ : syracuseStep 2932625 = 2199469) B2199469
theorem B2604977 : Blo 1156638 2604977 := bstep (se 2 (by rfl) ⟨976866, by rfl⟩ : syracuseStep 2604977 = 1953733) B1953733
theorem B2604995 : Blo 1156638 2604995 := bstep (se 1 (by rfl) ⟨1953746, by rfl⟩ : syracuseStep 2604995 = 3907493) B3907493
theorem B1392611 : Blo 1156638 1392611 := bstep (se 1 (by rfl) ⟨1044458, by rfl⟩ : syracuseStep 1392611 = 2088917) B2088917
theorem B3620945 : Blo 1156638 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B3915917 : Blo 1156638 3915917 := bstep (se 3 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 3915917 = 1468469) B1468469
theorem B2474147 : Blo 1156638 2474147 := bstep (se 1 (by rfl) ⟨1855610, by rfl⟩ : syracuseStep 2474147 = 3711221) B3711221
theorem B3915971 : Blo 1156638 3915971 := bstep (se 1 (by rfl) ⟨2936978, by rfl⟩ : syracuseStep 3915971 = 5873957) B5873957
theorem B2605265 : Blo 1156638 2605265 := bstep (se 2 (by rfl) ⟨976974, by rfl⟩ : syracuseStep 2605265 = 1953949) B1953949
theorem B1982675 : Blo 1156638 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B2605283 : Blo 1156638 2605283 := bstep (se 1 (by rfl) ⟨1953962, by rfl⟩ : syracuseStep 2605283 = 3907925) B3907925
theorem B3916241 : Blo 1156638 3916241 := bstep (se 2 (by rfl) ⟨1468590, by rfl⟩ : syracuseStep 3916241 = 2937181) B2937181
theorem B2605553 : Blo 1156638 2605553 := bstep (se 2 (by rfl) ⟨977082, by rfl⟩ : syracuseStep 2605553 = 1954165) B1954165
theorem B2605571 : Blo 1156638 2605571 := bstep (se 1 (by rfl) ⟨1954178, by rfl⟩ : syracuseStep 2605571 = 3908357) B3908357
theorem B3293713 : Blo 1156638 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B3129905 : Blo 1156638 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B2474659 : Blo 1156638 2474659 := bstep (se 1 (by rfl) ⟨1855994, by rfl⟩ : syracuseStep 2474659 = 3711989) B3711989
theorem B2605841 : Blo 1156638 2605841 := bstep (se 2 (by rfl) ⟨977190, by rfl⟩ : syracuseStep 2605841 = 1954381) B1954381
theorem B2605859 : Blo 1156638 2605859 := bstep (se 1 (by rfl) ⟨1954394, by rfl⟩ : syracuseStep 2605859 = 3908789) B3908789
theorem B2933617 : Blo 1156638 2933617 := bstep (se 2 (by rfl) ⟨1100106, by rfl⟩ : syracuseStep 2933617 = 2200213) B2200213
theorem B3130285 : Blo 1156638 3130285 := bstep (se 3 (by rfl) ⟨586928, by rfl⟩ : syracuseStep 3130285 = 1173857) B1173857
theorem B3916781 : Blo 1156638 3916781 := bstep (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) B1468793
theorem B3916835 : Blo 1156638 3916835 := bstep (se 1 (by rfl) ⟨2937626, by rfl⟩ : syracuseStep 3916835 = 5875253) B5875253
theorem B2606129 : Blo 1156638 2606129 := bstep (se 2 (by rfl) ⟨977298, by rfl⟩ : syracuseStep 2606129 = 1954597) B1954597
theorem B2606147 : Blo 1156638 2606147 := bstep (se 1 (by rfl) ⟨1954610, by rfl⟩ : syracuseStep 2606147 = 3909221) B3909221
theorem B6603875 : Blo 1156638 6603875 := bstep (se 1 (by rfl) ⟨4952906, by rfl⟩ : syracuseStep 6603875 = 9905813) B9905813
theorem B2933891 : Blo 1156638 2933891 := bstep (se 1 (by rfl) ⟨2200418, by rfl⟩ : syracuseStep 2933891 = 4400837) B4400837
theorem B2507939 : Blo 1156638 2507939 := bstep (se 1 (by rfl) ⟨1880954, by rfl⟩ : syracuseStep 2507939 = 3761909) B3761909
theorem B3917105 : Blo 1156638 3917105 := bstep (se 2 (by rfl) ⟨1468914, by rfl⟩ : syracuseStep 3917105 = 2937829) B2937829
theorem B2934083 : Blo 1156638 2934083 := bstep (se 1 (by rfl) ⟨2200562, by rfl⟩ : syracuseStep 2934083 = 4401125) B4401125
theorem B2606417 : Blo 1156638 2606417 := bstep (se 2 (by rfl) ⟨977406, by rfl⟩ : syracuseStep 2606417 = 1954813) B1954813
theorem B2606435 : Blo 1156638 2606435 := bstep (se 1 (by rfl) ⟨1954826, by rfl⟩ : syracuseStep 2606435 = 3909653) B3909653
theorem B2475377 : Blo 1156638 2475377 := bstep (se 2 (by rfl) ⟨928266, by rfl⟩ : syracuseStep 2475377 = 1856533) B1856533
theorem B1852913 : Blo 1156638 1852913 := bstep (se 2 (by rfl) ⟨694842, by rfl⟩ : syracuseStep 1852913 = 1389685) B1389685
theorem B11879921 : Blo 1156638 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B19809845 : Blo 1156638 19809845 := bstep (se 5 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 19809845 = 1857173) B1857173
theorem B2606705 : Blo 1156638 2606705 := bstep (se 2 (by rfl) ⟨977514, by rfl⟩ : syracuseStep 2606705 = 1955029) B1955029
theorem B2606723 : Blo 1156638 2606723 := bstep (se 1 (by rfl) ⟨1955042, by rfl⟩ : syracuseStep 2606723 = 3910085) B3910085
theorem B3294989 : Blo 1156638 3294989 := bstep (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) B1235621
theorem B3131149 : Blo 1156638 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B1853329 : Blo 1156638 1853329 := bstep (se 2 (by rfl) ⟨694998, by rfl⟩ : syracuseStep 1853329 = 1389997) B1389997
theorem B2606993 : Blo 1156638 2606993 := bstep (se 2 (by rfl) ⟨977622, by rfl⟩ : syracuseStep 2606993 = 1955245) B1955245
theorem B2607011 : Blo 1156638 2607011 := bstep (se 1 (by rfl) ⟨1955258, by rfl⟩ : syracuseStep 2607011 = 3910517) B3910517
theorem B3295171 : Blo 1156638 3295171 := bstep (se 1 (by rfl) ⟨2471378, by rfl⟩ : syracuseStep 3295171 = 4942757) B4942757
theorem B3295217 : Blo 1156638 3295217 := bstep (se 2 (by rfl) ⟨1235706, by rfl⟩ : syracuseStep 3295217 = 2471413) B2471413
theorem B1951843 : Blo 1156638 1951843 := bstep (se 1 (by rfl) ⟨1463882, by rfl⟩ : syracuseStep 1951843 = 2927765) B2927765
theorem B2476163 : Blo 1156638 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B2607281 : Blo 1156638 2607281 := bstep (se 2 (by rfl) ⟨977730, by rfl⟩ : syracuseStep 2607281 = 1955461) B1955461
theorem B2607299 : Blo 1156638 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B1951985 : Blo 1156638 1951985 := bstep (se 2 (by rfl) ⟨731994, by rfl⟩ : syracuseStep 1951985 = 1463989) B1463989
theorem B2935025 : Blo 1156638 2935025 := bstep (se 2 (by rfl) ⟨1100634, by rfl⟩ : syracuseStep 2935025 = 2201269) B2201269
theorem B2935075 : Blo 1156638 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B1952113 : Blo 1156638 1952113 := bstep (se 2 (by rfl) ⟨732042, by rfl⟩ : syracuseStep 1952113 = 1464085) B1464085
theorem B1952147 : Blo 1156638 1952147 := bstep (se 1 (by rfl) ⟨1464110, by rfl⟩ : syracuseStep 1952147 = 2928221) B2928221
theorem B2935217 : Blo 1156638 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B2607569 : Blo 1156638 2607569 := bstep (se 2 (by rfl) ⟨977838, by rfl⟩ : syracuseStep 2607569 = 1955677) B1955677
theorem B2607587 : Blo 1156638 2607587 := bstep (se 1 (by rfl) ⟨1955690, by rfl⟩ : syracuseStep 2607587 = 3911381) B3911381
theorem B1952275 : Blo 1156638 1952275 := bstep (se 1 (by rfl) ⟨1464206, by rfl⟩ : syracuseStep 1952275 = 2928413) B2928413
theorem B3132035 : Blo 1156638 3132035 := bstep (se 1 (by rfl) ⟨2349026, by rfl⟩ : syracuseStep 3132035 = 4698053) B4698053
theorem B1952417 : Blo 1156638 1952417 := bstep (se 2 (by rfl) ⟨732156, by rfl⟩ : syracuseStep 1952417 = 1464313) B1464313
theorem B2607857 : Blo 1156638 2607857 := bstep (se 2 (by rfl) ⟨977946, by rfl⟩ : syracuseStep 2607857 = 1955893) B1955893
theorem B2607875 : Blo 1156638 2607875 := bstep (se 1 (by rfl) ⟨1955906, by rfl⟩ : syracuseStep 2607875 = 3911813) B3911813
theorem B1854227 : Blo 1156638 1854227 := bstep (se 1 (by rfl) ⟨1390670, by rfl⟩ : syracuseStep 1854227 = 2781341) B2781341
theorem B80169749 : Blo 1156638 80169749 := bstep (se 6 (by rfl) ⟨1878978, by rfl⟩ : syracuseStep 80169749 = 3757957) B3757957
theorem B1952545 : Blo 1156638 1952545 := bstep (se 2 (by rfl) ⟨732204, by rfl⟩ : syracuseStep 1952545 = 1464409) B1464409
theorem B3132209 : Blo 1156638 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B1952579 : Blo 1156638 1952579 := bstep (se 1 (by rfl) ⟨1464434, by rfl⟩ : syracuseStep 1952579 = 2928869) B2928869
theorem B3132337 : Blo 1156638 3132337 := bstep (se 2 (by rfl) ⟨1174626, by rfl⟩ : syracuseStep 3132337 = 2349253) B2349253
theorem B1952707 : Blo 1156638 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B1854451 : Blo 1156638 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B2608145 : Blo 1156638 2608145 := bstep (se 2 (by rfl) ⟨978054, by rfl⟩ : syracuseStep 2608145 = 1956109) B1956109
theorem B2608163 : Blo 1156638 2608163 := bstep (se 1 (by rfl) ⟨1956122, by rfl⟩ : syracuseStep 2608163 = 3912245) B3912245
theorem B1952849 : Blo 1156638 1952849 := bstep (se 2 (by rfl) ⟨732318, by rfl⟩ : syracuseStep 1952849 = 1464637) B1464637
theorem B2477137 : Blo 1156638 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B1952977 : Blo 1156638 1952977 := bstep (se 2 (by rfl) ⟨732366, by rfl⟩ : syracuseStep 1952977 = 1464733) B1464733
theorem B11128049 : Blo 1156638 11128049 := bstep (se 2 (by rfl) ⟨4173018, by rfl⟩ : syracuseStep 11128049 = 8346037) B8346037
theorem B1953011 : Blo 1156638 1953011 := bstep (se 1 (by rfl) ⟨1464758, by rfl⟩ : syracuseStep 1953011 = 2929517) B2929517
theorem B2608433 : Blo 1156638 2608433 := bstep (se 2 (by rfl) ⟨978162, by rfl⟩ : syracuseStep 2608433 = 1956325) B1956325
theorem B2608451 : Blo 1156638 2608451 := bstep (se 1 (by rfl) ⟨1956338, by rfl⟩ : syracuseStep 2608451 = 3912677) B3912677
theorem B2477393 : Blo 1156638 2477393 := bstep (se 2 (by rfl) ⟨929022, by rfl⟩ : syracuseStep 2477393 = 1858045) B1858045
theorem B1953139 : Blo 1156638 1953139 := bstep (se 1 (by rfl) ⟨1464854, by rfl⟩ : syracuseStep 1953139 = 2929709) B2929709
theorem B2936209 : Blo 1156638 2936209 := bstep (se 2 (by rfl) ⟨1101078, by rfl⟩ : syracuseStep 2936209 = 2202157) B2202157
theorem B3296675 : Blo 1156638 3296675 := bstep (se 1 (by rfl) ⟨2472506, by rfl⟩ : syracuseStep 3296675 = 4945013) B4945013
theorem B1953281 : Blo 1156638 1953281 := bstep (se 2 (by rfl) ⟨732480, by rfl⟩ : syracuseStep 1953281 = 1464961) B1464961
theorem B2346545 : Blo 1156638 2346545 := bstep (se 2 (by rfl) ⟨879954, by rfl⟩ : syracuseStep 2346545 = 1759909) B1759909
theorem B2608721 : Blo 1156638 2608721 := bstep (se 2 (by rfl) ⟨978270, by rfl⟩ : syracuseStep 2608721 = 1956541) B1956541
theorem B2608739 : Blo 1156638 2608739 := bstep (se 1 (by rfl) ⟨1956554, by rfl⟩ : syracuseStep 2608739 = 3913109) B3913109
theorem B1953409 : Blo 1156638 1953409 := bstep (se 2 (by rfl) ⟨732528, by rfl⟩ : syracuseStep 1953409 = 1465057) B1465057
theorem B1953443 : Blo 1156638 1953443 := bstep (se 1 (by rfl) ⟨1465082, by rfl⟩ : syracuseStep 1953443 = 2930165) B2930165
theorem B2936483 : Blo 1156638 2936483 := bstep (se 1 (by rfl) ⟨2202362, by rfl⟩ : syracuseStep 2936483 = 4404725) B4404725
theorem B22236869 : Blo 1156638 22236869 := bstep (se 4 (by rfl) ⟨2084706, by rfl⟩ : syracuseStep 22236869 = 4169413) B4169413
theorem B1953571 : Blo 1156638 1953571 := bstep (se 1 (by rfl) ⟨1465178, by rfl⟩ : syracuseStep 1953571 = 2930357) B2930357
theorem B1429331 : Blo 1156638 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B2936675 : Blo 1156638 2936675 := bstep (se 1 (by rfl) ⟨2202506, by rfl⟩ : syracuseStep 2936675 = 4405013) B4405013
theorem B2609009 : Blo 1156638 2609009 := bstep (se 2 (by rfl) ⟨978378, by rfl⟩ : syracuseStep 2609009 = 1956757) B1956757
theorem B2609027 : Blo 1156638 2609027 := bstep (se 1 (by rfl) ⟨1956770, by rfl⟩ : syracuseStep 2609027 = 3913541) B3913541
theorem B1953713 : Blo 1156638 1953713 := bstep (se 2 (by rfl) ⟨732642, by rfl⟩ : syracuseStep 1953713 = 1465285) B1465285
theorem B14864309 : Blo 1156638 14864309 := bstep (se 5 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 14864309 = 1393529) B1393529
theorem B1855457 : Blo 1156638 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B1953841 : Blo 1156638 1953841 := bstep (se 2 (by rfl) ⟨732690, by rfl⟩ : syracuseStep 1953841 = 1465381) B1465381
theorem B1953875 : Blo 1156638 1953875 := bstep (se 1 (by rfl) ⟨1465406, by rfl⟩ : syracuseStep 1953875 = 2930813) B2930813
theorem B2609297 : Blo 1156638 2609297 := bstep (se 2 (by rfl) ⟨978486, by rfl⟩ : syracuseStep 2609297 = 1956973) B1956973
theorem B1855649 : Blo 1156638 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B2609315 : Blo 1156638 2609315 := bstep (se 1 (by rfl) ⟨1956986, by rfl⟩ : syracuseStep 2609315 = 3913973) B3913973
theorem B1954003 : Blo 1156638 1954003 := bstep (se 1 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 1954003 = 2931005) B2931005
theorem B6607109 : Blo 1156638 6607109 := bstep (se 4 (by rfl) ⟨619416, by rfl⟩ : syracuseStep 6607109 = 1238833) B1238833
theorem B3526993 : Blo 1156638 3526993 := bstep (se 2 (by rfl) ⟨1322622, by rfl⟩ : syracuseStep 3526993 = 2645245) B2645245
theorem B1954145 : Blo 1156638 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B3756401 : Blo 1156638 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B2609585 : Blo 1156638 2609585 := bstep (se 2 (by rfl) ⟨978594, by rfl⟩ : syracuseStep 2609585 = 1957189) B1957189
theorem B2609603 : Blo 1156638 2609603 := bstep (se 1 (by rfl) ⟨1957202, by rfl⟩ : syracuseStep 2609603 = 3914405) B3914405
theorem B1954273 : Blo 1156638 1954273 := bstep (se 2 (by rfl) ⟨732852, by rfl⟩ : syracuseStep 1954273 = 1465705) B1465705
theorem B3133937 : Blo 1156638 3133937 := bstep (se 2 (by rfl) ⟨1175226, by rfl⟩ : syracuseStep 3133937 = 2350453) B2350453
theorem B1954307 : Blo 1156638 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B2970179 : Blo 1156638 2970179 := bstep (se 1 (by rfl) ⟨2227634, by rfl⟩ : syracuseStep 2970179 = 4455269) B4455269
theorem B2478691 : Blo 1156638 2478691 := bstep (se 1 (by rfl) ⟨1859018, by rfl⟩ : syracuseStep 2478691 = 3718037) B3718037
theorem B3297905 : Blo 1156638 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B1954435 : Blo 1156638 1954435 := bstep (se 1 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 1954435 = 2931653) B2931653
theorem B5558989 : Blo 1156638 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B6607565 : Blo 1156638 6607565 := bstep (se 3 (by rfl) ⟨1238918, by rfl⟩ : syracuseStep 6607565 = 2477837) B2477837
theorem B2609873 : Blo 1156638 2609873 := bstep (se 2 (by rfl) ⟨978702, by rfl⟩ : syracuseStep 2609873 = 1957405) B1957405
theorem B2609891 : Blo 1156638 2609891 := bstep (se 1 (by rfl) ⟨1957418, by rfl⟩ : syracuseStep 2609891 = 3914837) B3914837
theorem B1954577 : Blo 1156638 1954577 := bstep (se 2 (by rfl) ⟨732966, by rfl⟩ : syracuseStep 1954577 = 1465933) B1465933
theorem B2937617 : Blo 1156638 2937617 := bstep (se 2 (by rfl) ⟨1101606, by rfl⟩ : syracuseStep 2937617 = 2203213) B2203213
theorem B2937667 : Blo 1156638 2937667 := bstep (se 1 (by rfl) ⟨2203250, by rfl⟩ : syracuseStep 2937667 = 4406501) B4406501
theorem B2085745 : Blo 1156638 2085745 := bstep (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) B1564309
theorem B1954705 : Blo 1156638 1954705 := bstep (se 2 (by rfl) ⟨733014, by rfl⟩ : syracuseStep 1954705 = 1466029) B1466029
theorem B1954739 : Blo 1156638 1954739 := bstep (se 1 (by rfl) ⟨1466054, by rfl⟩ : syracuseStep 1954739 = 2932109) B2932109
theorem B3134413 : Blo 1156638 3134413 := bstep (se 3 (by rfl) ⟨587702, by rfl⟩ : syracuseStep 3134413 = 1175405) B1175405
theorem B2937809 : Blo 1156638 2937809 := bstep (se 2 (by rfl) ⟨1101678, by rfl⟩ : syracuseStep 2937809 = 2203357) B2203357
theorem B2610161 : Blo 1156638 2610161 := bstep (se 2 (by rfl) ⟨978810, by rfl⟩ : syracuseStep 2610161 = 1957621) B1957621
theorem B2610179 : Blo 1156638 2610179 := bstep (se 1 (by rfl) ⟨1957634, by rfl⟩ : syracuseStep 2610179 = 3915269) B3915269
theorem B1954867 : Blo 1156638 1954867 := bstep (se 1 (by rfl) ⟨1466150, by rfl⟩ : syracuseStep 1954867 = 2932301) B2932301
theorem B13554787 : Blo 1156638 13554787 := bstep (se 1 (by rfl) ⟨10166090, by rfl⟩ : syracuseStep 13554787 = 20332181) B20332181
theorem B3134609 : Blo 1156638 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B1955009 : Blo 1156638 1955009 := bstep (se 2 (by rfl) ⟨733128, by rfl⟩ : syracuseStep 1955009 = 1466257) B1466257
theorem B2610449 : Blo 1156638 2610449 := bstep (se 2 (by rfl) ⟨978918, by rfl⟩ : syracuseStep 2610449 = 1957837) B1957837
theorem B2610467 : Blo 1156638 2610467 := bstep (se 1 (by rfl) ⟨1957850, by rfl⟩ : syracuseStep 2610467 = 3915701) B3915701
theorem B1955137 : Blo 1156638 1955137 := bstep (se 2 (by rfl) ⟨733176, by rfl⟩ : syracuseStep 1955137 = 1466353) B1466353
theorem B1955171 : Blo 1156638 1955171 := bstep (se 1 (by rfl) ⟨1466378, by rfl⟩ : syracuseStep 1955171 = 2932757) B2932757
theorem B1955299 : Blo 1156638 1955299 := bstep (se 1 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 1955299 = 2932949) B2932949
theorem B2610737 : Blo 1156638 2610737 := bstep (se 2 (by rfl) ⟨979026, by rfl⟩ : syracuseStep 2610737 = 1958053) B1958053
theorem B2610755 : Blo 1156638 2610755 := bstep (se 1 (by rfl) ⟨1958066, by rfl⟩ : syracuseStep 2610755 = 3916133) B3916133
theorem B1955441 : Blo 1156638 1955441 := bstep (se 2 (by rfl) ⟨733290, by rfl⟩ : syracuseStep 1955441 = 1466581) B1466581
theorem B1463923 : Blo 1156638 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B8345285 : Blo 1156638 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B1857251 : Blo 1156638 1857251 := bstep (se 1 (by rfl) ⟨1392938, by rfl⟩ : syracuseStep 1857251 = 2785877) B2785877
theorem B1955569 : Blo 1156638 1955569 := bstep (se 2 (by rfl) ⟨733338, by rfl⟩ : syracuseStep 1955569 = 1466677) B1466677
theorem B1955603 : Blo 1156638 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B2611025 : Blo 1156638 2611025 := bstep (se 2 (by rfl) ⟨979134, by rfl⟩ : syracuseStep 2611025 = 1958269) B1958269
theorem B2611043 : Blo 1156638 2611043 := bstep (se 1 (by rfl) ⟨1958282, by rfl⟩ : syracuseStep 2611043 = 3916565) B3916565
theorem B1955731 : Blo 1156638 1955731 := bstep (se 1 (by rfl) ⟨1466798, by rfl⟩ : syracuseStep 1955731 = 2933597) B2933597
theorem B1955873 : Blo 1156638 1955873 := bstep (se 2 (by rfl) ⟨733452, by rfl⟩ : syracuseStep 1955873 = 1466905) B1466905
theorem B3299363 : Blo 1156638 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B7428131 : Blo 1156638 7428131 := bstep (se 1 (by rfl) ⟨5571098, by rfl⟩ : syracuseStep 7428131 = 11142197) B11142197
theorem B1464419 : Blo 1156638 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1857635 : Blo 1156638 1857635 := bstep (se 1 (by rfl) ⟨1393226, by rfl⟩ : syracuseStep 1857635 = 2786453) B2786453
theorem B5560433 : Blo 1156638 5560433 := bstep (se 2 (by rfl) ⟨2085162, by rfl⟩ : syracuseStep 5560433 = 4170325) B4170325
theorem B2611313 : Blo 1156638 2611313 := bstep (se 2 (by rfl) ⟨979242, by rfl⟩ : syracuseStep 2611313 = 1958485) B1958485
theorem B2611331 : Blo 1156638 2611331 := bstep (se 1 (by rfl) ⟨1958498, by rfl⟩ : syracuseStep 2611331 = 3916997) B3916997
theorem B1956001 : Blo 1156638 1956001 := bstep (se 2 (by rfl) ⟨733500, by rfl⟩ : syracuseStep 1956001 = 1467001) B1467001
theorem B1956035 : Blo 1156638 1956035 := bstep (se 1 (by rfl) ⟨1467026, by rfl⟩ : syracuseStep 1956035 = 2934053) B2934053
theorem B37607651 : Blo 1156638 37607651 := bstep (se 1 (by rfl) ⟨28205738, by rfl⟩ : syracuseStep 37607651 = 56411477) B56411477
theorem B1857763 : Blo 1156638 1857763 := bstep (se 1 (by rfl) ⟨1393322, by rfl⟩ : syracuseStep 1857763 = 2786645) B2786645
theorem B8476913 : Blo 1156638 8476913 := bstep (se 2 (by rfl) ⟨3178842, by rfl⟩ : syracuseStep 8476913 = 6357685) B6357685
theorem B1956163 : Blo 1156638 1956163 := bstep (se 1 (by rfl) ⟨1467122, by rfl⟩ : syracuseStep 1956163 = 2934245) B2934245
theorem B9525617 : Blo 1156638 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B5855651 : Blo 1156638 5855651 := bstep (se 1 (by rfl) ⟨4391738, by rfl⟩ : syracuseStep 5855651 = 8783477) B8783477
theorem B1956305 : Blo 1156638 1956305 := bstep (se 2 (by rfl) ⟨733614, by rfl⟩ : syracuseStep 1956305 = 1467229) B1467229
theorem B3135971 : Blo 1156638 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B1235459 : Blo 1156638 1235459 := bstep (se 1 (by rfl) ⟨926594, by rfl⟩ : syracuseStep 1235459 = 1853189) B1853189
theorem B1956433 : Blo 1156638 1956433 := bstep (se 2 (by rfl) ⟨733662, by rfl⟩ : syracuseStep 1956433 = 1467325) B1467325
theorem B14113379 : Blo 1156638 14113379 := bstep (se 1 (by rfl) ⟨10585034, by rfl⟩ : syracuseStep 14113379 = 21170069) B21170069
theorem B1956467 : Blo 1156638 1956467 := bstep (se 1 (by rfl) ⟨1467350, by rfl⟩ : syracuseStep 1956467 = 2934701) B2934701
theorem B1956595 : Blo 1156638 1956595 := bstep (se 1 (by rfl) ⟨1467446, by rfl⟩ : syracuseStep 1956595 = 2934893) B2934893
theorem B1301251 : Blo 1156638 1301251 := bstep (se 1 (by rfl) ⟨975938, by rfl⟩ : syracuseStep 1301251 = 1951877) B1951877
theorem B1465123 : Blo 1156638 1465123 := bstep (se 1 (by rfl) ⟨1098842, by rfl⟩ : syracuseStep 1465123 = 2197685) B2197685
theorem B3300173 : Blo 1156638 3300173 := bstep (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) B1237565
theorem B1956737 : Blo 1156638 1956737 := bstep (se 2 (by rfl) ⟨733776, by rfl⟩ : syracuseStep 1956737 = 1467553) B1467553
theorem B1465219 : Blo 1156638 1465219 := bstep (se 1 (by rfl) ⟨1098914, by rfl⟩ : syracuseStep 1465219 = 2197829) B2197829
theorem B1301395 : Blo 1156638 1301395 := bstep (se 1 (by rfl) ⟨976046, by rfl⟩ : syracuseStep 1301395 = 1952093) B1952093
theorem B1858481 : Blo 1156638 1858481 := bstep (se 2 (by rfl) ⟨696930, by rfl⟩ : syracuseStep 1858481 = 1393861) B1393861
theorem B8805347 : Blo 1156638 8805347 := bstep (se 1 (by rfl) ⟨6604010, by rfl⟩ : syracuseStep 8805347 = 13208021) B13208021
theorem B1956865 : Blo 1156638 1956865 := bstep (se 2 (by rfl) ⟨733824, by rfl⟩ : syracuseStep 1956865 = 1467649) B1467649
theorem B3300365 : Blo 1156638 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B1301539 : Blo 1156638 1301539 := bstep (se 1 (by rfl) ⟨976154, by rfl⟩ : syracuseStep 1301539 = 1952309) B1952309
theorem B1956899 : Blo 1156638 1956899 := bstep (se 1 (by rfl) ⟨1467674, by rfl⟩ : syracuseStep 1956899 = 2935349) B2935349
theorem B13196357 : Blo 1156638 13196357 := bstep (se 4 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 13196357 = 2474317) B2474317
theorem B6020173 : Blo 1156638 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B3759203 : Blo 1156638 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B1858673 : Blo 1156638 1858673 := bstep (se 2 (by rfl) ⟨697002, by rfl⟩ : syracuseStep 1858673 = 1394005) B1394005
theorem B1957027 : Blo 1156638 1957027 := bstep (se 1 (by rfl) ⟨1467770, by rfl⟩ : syracuseStep 1957027 = 2935541) B2935541
theorem B1301683 : Blo 1156638 1301683 := bstep (se 1 (by rfl) ⟨976262, by rfl⟩ : syracuseStep 1301683 = 1952525) B1952525
theorem B5856461 : Blo 1156638 5856461 := bstep (se 3 (by rfl) ⟨1098086, by rfl⟩ : syracuseStep 5856461 = 2196173) B2196173
theorem B1957169 : Blo 1156638 1957169 := bstep (se 2 (by rfl) ⟨733938, by rfl⟩ : syracuseStep 1957169 = 1467877) B1467877
theorem B1301827 : Blo 1156638 1301827 := bstep (se 1 (by rfl) ⟨976370, by rfl⟩ : syracuseStep 1301827 = 1952741) B1952741
theorem B1465715 : Blo 1156638 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B2088355 : Blo 1156638 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B1957297 : Blo 1156638 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B1301971 : Blo 1156638 1301971 := bstep (se 1 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 1301971 = 1952957) B1952957
theorem B1957331 : Blo 1156638 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B1957459 : Blo 1156638 1957459 := bstep (se 1 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 1957459 = 2936189) B2936189
theorem B1302115 : Blo 1156638 1302115 := bstep (se 1 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 1302115 = 1953173) B1953173
theorem B11886193 : Blo 1156638 11886193 := bstep (se 2 (by rfl) ⟨4457322, by rfl⟩ : syracuseStep 11886193 = 8914645) B8914645
theorem B1236595 : Blo 1156638 1236595 := bstep (se 1 (by rfl) ⟨927446, by rfl⟩ : syracuseStep 1236595 = 1854893) B1854893
theorem B24141509 : Blo 1156638 24141509 := bstep (se 4 (by rfl) ⟨2263266, by rfl⟩ : syracuseStep 24141509 = 4526533) B4526533
theorem B1957601 : Blo 1156638 1957601 := bstep (se 2 (by rfl) ⟨734100, by rfl⟩ : syracuseStep 1957601 = 1468201) B1468201
theorem B1302259 : Blo 1156638 1302259 := bstep (se 1 (by rfl) ⟨976694, by rfl⟩ : syracuseStep 1302259 = 1953389) B1953389
theorem B1761059 : Blo 1156638 1761059 := bstep (se 1 (by rfl) ⟨1320794, by rfl⟩ : syracuseStep 1761059 = 2641589) B2641589
theorem B1957729 : Blo 1156638 1957729 := bstep (se 2 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 1957729 = 1468297) B1468297
theorem B1302403 : Blo 1156638 1302403 := bstep (se 1 (by rfl) ⟨976802, by rfl⟩ : syracuseStep 1302403 = 1953605) B1953605
theorem B1957763 : Blo 1156638 1957763 := bstep (se 1 (by rfl) ⟨1468322, by rfl⟩ : syracuseStep 1957763 = 2936645) B2936645
theorem B3301357 : Blo 1156638 3301357 := bstep (se 3 (by rfl) ⟨619004, by rfl⟩ : syracuseStep 3301357 = 1238009) B1238009
theorem B7430129 : Blo 1156638 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B1957891 : Blo 1156638 1957891 := bstep (se 1 (by rfl) ⟨1468418, by rfl⟩ : syracuseStep 1957891 = 2936837) B2936837
theorem B1302547 : Blo 1156638 1302547 := bstep (se 1 (by rfl) ⟨976910, by rfl⟩ : syracuseStep 1302547 = 1953821) B1953821
theorem B1466419 : Blo 1156638 1466419 := bstep (se 1 (by rfl) ⟨1099814, by rfl⟩ : syracuseStep 1466419 = 2199629) B2199629
theorem B1958033 : Blo 1156638 1958033 := bstep (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) B1468525
theorem B1466515 : Blo 1156638 1466515 := bstep (se 1 (by rfl) ⟨1099886, by rfl⟩ : syracuseStep 1466515 = 2199773) B2199773
theorem B1302691 : Blo 1156638 1302691 := bstep (se 1 (by rfl) ⟨977018, by rfl⟩ : syracuseStep 1302691 = 1954037) B1954037
theorem B11133197 : Blo 1156638 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B1958161 : Blo 1156638 1958161 := bstep (se 2 (by rfl) ⟨734310, by rfl⟩ : syracuseStep 1958161 = 1468621) B1468621
theorem B1302835 : Blo 1156638 1302835 := bstep (se 1 (by rfl) ⟨977126, by rfl⟩ : syracuseStep 1302835 = 1954253) B1954253
theorem B1958195 : Blo 1156638 1958195 := bstep (se 1 (by rfl) ⟨1468646, by rfl⟩ : syracuseStep 1958195 = 2937293) B2937293
theorem B1958323 : Blo 1156638 1958323 := bstep (se 1 (by rfl) ⟨1468742, by rfl⟩ : syracuseStep 1958323 = 2937485) B2937485
theorem B1302979 : Blo 1156638 1302979 := bstep (se 1 (by rfl) ⟨977234, by rfl⟩ : syracuseStep 1302979 = 1954469) B1954469
theorem B1237475 : Blo 1156638 1237475 := bstep (se 1 (by rfl) ⟨928106, by rfl⟩ : syracuseStep 1237475 = 1856213) B1856213
theorem B1958465 : Blo 1156638 1958465 := bstep (se 2 (by rfl) ⟨734424, by rfl⟩ : syracuseStep 1958465 = 1468849) B1468849
theorem B1303123 : Blo 1156638 1303123 := bstep (se 1 (by rfl) ⟨977342, by rfl⟩ : syracuseStep 1303123 = 1954685) B1954685
theorem B1237603 : Blo 1156638 1237603 := bstep (se 1 (by rfl) ⟨928202, by rfl⟩ : syracuseStep 1237603 = 1856405) B1856405
theorem B1467011 : Blo 1156638 1467011 := bstep (se 1 (by rfl) ⟨1100258, by rfl⟩ : syracuseStep 1467011 = 2200517) B2200517
theorem B1303267 : Blo 1156638 1303267 := bstep (se 1 (by rfl) ⟨977450, by rfl⟩ : syracuseStep 1303267 = 1954901) B1954901
theorem B1303411 : Blo 1156638 1303411 := bstep (se 1 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 1303411 = 1955117) B1955117
theorem B1303555 : Blo 1156638 1303555 := bstep (se 1 (by rfl) ⟨977666, by rfl⟩ : syracuseStep 1303555 = 1955333) B1955333
theorem B1303699 : Blo 1156638 1303699 := bstep (se 1 (by rfl) ⟨977774, by rfl⟩ : syracuseStep 1303699 = 1955549) B1955549
theorem B1303843 : Blo 1156638 1303843 := bstep (se 1 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 1303843 = 1955765) B1955765
theorem B1467715 : Blo 1156638 1467715 := bstep (se 1 (by rfl) ⟨1100786, by rfl⟩ : syracuseStep 1467715 = 2201573) B2201573
theorem B1172819 : Blo 1156638 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B1238419 : Blo 1156638 1238419 := bstep (se 1 (by rfl) ⟨928814, by rfl⟩ : syracuseStep 1238419 = 1857629) B1857629
theorem B1467811 : Blo 1156638 1467811 := bstep (se 1 (by rfl) ⟨1100858, by rfl⟩ : syracuseStep 1467811 = 2201717) B2201717
theorem B1303987 : Blo 1156638 1303987 := bstep (se 1 (by rfl) ⟨977990, by rfl⟩ : syracuseStep 1303987 = 1955981) B1955981
theorem B1304131 : Blo 1156638 1304131 := bstep (se 1 (by rfl) ⟨978098, by rfl⟩ : syracuseStep 1304131 = 1956197) B1956197
theorem B4941425 : Blo 1156638 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B7431821 : Blo 1156638 7431821 := bstep (se 3 (by rfl) ⟨1393466, by rfl⟩ : syracuseStep 7431821 = 2786933) B2786933
theorem B3303089 : Blo 1156638 3303089 := bstep (se 2 (by rfl) ⟨1238658, by rfl⟩ : syracuseStep 3303089 = 2477317) B2477317
theorem B1304275 : Blo 1156638 1304275 := bstep (se 1 (by rfl) ⟨978206, by rfl⟩ : syracuseStep 1304275 = 1956413) B1956413
theorem B2090755 : Blo 1156638 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B1304419 : Blo 1156638 1304419 := bstep (se 1 (by rfl) ⟨978314, by rfl⟩ : syracuseStep 1304419 = 1956629) B1956629
theorem B3303281 : Blo 1156638 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1468307 : Blo 1156638 1468307 := bstep (se 1 (by rfl) ⟨1101230, by rfl⟩ : syracuseStep 1468307 = 2202461) B2202461
theorem B14837701 : Blo 1156638 14837701 := bstep (se 4 (by rfl) ⟨1391034, by rfl⟩ : syracuseStep 14837701 = 2782069) B2782069
theorem B1304563 : Blo 1156638 1304563 := bstep (se 1 (by rfl) ⟨978422, by rfl⟩ : syracuseStep 1304563 = 1956845) B1956845
theorem B5859377 : Blo 1156638 5859377 := bstep (se 2 (by rfl) ⟨2197266, by rfl⟩ : syracuseStep 5859377 = 4394533) B4394533
theorem B2779217 : Blo 1156638 2779217 := bstep (se 2 (by rfl) ⟨1042206, by rfl⟩ : syracuseStep 2779217 = 2084413) B2084413
theorem B1304707 : Blo 1156638 1304707 := bstep (se 1 (by rfl) ⟨978530, by rfl⟩ : syracuseStep 1304707 = 1957061) B1957061
theorem B25389283 : Blo 1156638 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B1304851 : Blo 1156638 1304851 := bstep (se 1 (by rfl) ⟨978638, by rfl⟩ : syracuseStep 1304851 = 1957277) B1957277
theorem B1304995 : Blo 1156638 1304995 := bstep (se 1 (by rfl) ⟨978746, by rfl⟩ : syracuseStep 1304995 = 1957493) B1957493
theorem B1305139 : Blo 1156638 1305139 := bstep (se 1 (by rfl) ⟨978854, by rfl⟩ : syracuseStep 1305139 = 1957709) B1957709
theorem B1305283 : Blo 1156638 1305283 := bstep (se 1 (by rfl) ⟨978962, by rfl⟩ : syracuseStep 1305283 = 1957925) B1957925
theorem B23751365 : Blo 1156638 23751365 := bstep (se 4 (by rfl) ⟨2226690, by rfl⟩ : syracuseStep 23751365 = 4453381) B4453381
theorem B3304273 : Blo 1156638 3304273 := bstep (se 2 (by rfl) ⟨1239102, by rfl⟩ : syracuseStep 3304273 = 2478205) B2478205
theorem B1305427 : Blo 1156638 1305427 := bstep (se 1 (by rfl) ⟨979070, by rfl⟩ : syracuseStep 1305427 = 1958141) B1958141
theorem B1764227 : Blo 1156638 1764227 := bstep (se 1 (by rfl) ⟨1323170, by rfl⟩ : syracuseStep 1764227 = 2646341) B2646341
theorem B1764275 : Blo 1156638 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B1305571 : Blo 1156638 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B1764385 : Blo 1156638 1764385 := bstep (se 2 (by rfl) ⟨661644, by rfl⟩ : syracuseStep 1764385 = 1323289) B1323289
theorem B3304547 : Blo 1156638 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B1305715 : Blo 1156638 1305715 := bstep (se 1 (by rfl) ⟨979286, by rfl⟩ : syracuseStep 1305715 = 1958573) B1958573
theorem B10022129 : Blo 1156638 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B3304739 : Blo 1156638 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B9530821 : Blo 1156638 9530821 := bstep (se 4 (by rfl) ⟨893514, by rfl⟩ : syracuseStep 9530821 = 1787029) B1787029
theorem B5860835 : Blo 1156638 5860835 := bstep (se 1 (by rfl) ⟨4395626, by rfl⟩ : syracuseStep 5860835 = 8791253) B8791253
theorem B3010097 : Blo 1156638 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B1568515 : Blo 1156638 1568515 := bstep (se 1 (by rfl) ⟨1176386, by rfl⟩ : syracuseStep 1568515 = 2352773) B2352773
theorem B8810693 : Blo 1156638 8810693 := bstep (se 4 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 8810693 = 1652005) B1652005
theorem B5861645 : Blo 1156638 5861645 := bstep (se 3 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 5861645 = 2198117) B2198117
theorem B4944397 : Blo 1156638 4944397 := bstep (se 3 (by rfl) ⟨927074, by rfl⟩ : syracuseStep 4944397 = 1854149) B1854149
theorem B2781859 : Blo 1156638 2781859 := bstep (se 1 (by rfl) ⟨2086394, by rfl⟩ : syracuseStep 2781859 = 4172789) B4172789
theorem B2781955 : Blo 1156638 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B13202189 : Blo 1156638 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B4944739 : Blo 1156638 4944739 := bstep (se 1 (by rfl) ⟨3708554, by rfl⟩ : syracuseStep 4944739 = 7417109) B7417109
theorem B2782147 : Blo 1156638 2782147 := bstep (se 1 (by rfl) ⟨2086610, by rfl⟩ : syracuseStep 2782147 = 4173221) B4173221
theorem B3437873 : Blo 1156638 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B21132913 : Blo 1156638 21132913 := bstep (se 2 (by rfl) ⟨7924842, by rfl⟩ : syracuseStep 21132913 = 15849685) B15849685
theorem B6256369 : Blo 1156638 6256369 := bstep (se 2 (by rfl) ⟨2346138, by rfl⟩ : syracuseStep 6256369 = 4692277) B4692277
theorem B8025925 : Blo 1156638 8025925 := bstep (se 4 (by rfl) ⟨752430, by rfl⟩ : syracuseStep 8025925 = 1504861) B1504861
theorem B2783089 : Blo 1156638 2783089 := bstep (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) B2087317
theorem B1734977 : Blo 1156638 1734977 := bstep (se 2 (by rfl) ⟨650616, by rfl⟩ : syracuseStep 1734977 = 1301233) B1301233
theorem B1734995 : Blo 1156638 1734995 := bstep (se 1 (by rfl) ⟨1301246, by rfl⟩ : syracuseStep 1734995 = 2602493) B2602493
theorem B1735025 : Blo 1156638 1735025 := bstep (se 2 (by rfl) ⟨650634, by rfl⟩ : syracuseStep 1735025 = 1301269) B1301269
theorem B1735043 : Blo 1156638 1735043 := bstep (se 1 (by rfl) ⟨1301282, by rfl⟩ : syracuseStep 1735043 = 2602565) B2602565
theorem B1735073 : Blo 1156638 1735073 := bstep (se 2 (by rfl) ⟨650652, by rfl⟩ : syracuseStep 1735073 = 1301305) B1301305
theorem B1735091 : Blo 1156638 1735091 := bstep (se 1 (by rfl) ⟨1301318, by rfl⟩ : syracuseStep 1735091 = 2602637) B2602637
theorem B1735121 : Blo 1156638 1735121 := bstep (se 2 (by rfl) ⟨650670, by rfl⟩ : syracuseStep 1735121 = 1301341) B1301341
theorem B1735139 : Blo 1156638 1735139 := bstep (se 1 (by rfl) ⟨1301354, by rfl⟩ : syracuseStep 1735139 = 2602709) B2602709
theorem B1735169 : Blo 1156638 1735169 := bstep (se 2 (by rfl) ⟨650688, by rfl⟩ : syracuseStep 1735169 = 1301377) B1301377
theorem B16087565 : Blo 1156638 16087565 := bstep (se 3 (by rfl) ⟨3016418, by rfl⟩ : syracuseStep 16087565 = 6032837) B6032837
theorem B1735187 : Blo 1156638 1735187 := bstep (se 1 (by rfl) ⟨1301390, by rfl⟩ : syracuseStep 1735187 = 2602781) B2602781
theorem B1735217 : Blo 1156638 1735217 := bstep (se 2 (by rfl) ⟨650706, by rfl⟩ : syracuseStep 1735217 = 1301413) B1301413
theorem B1735235 : Blo 1156638 1735235 := bstep (se 1 (by rfl) ⟨1301426, by rfl⟩ : syracuseStep 1735235 = 2602853) B2602853
theorem B1735265 : Blo 1156638 1735265 := bstep (se 2 (by rfl) ⟨650724, by rfl⟩ : syracuseStep 1735265 = 1301449) B1301449
theorem B1735283 : Blo 1156638 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B3766925 : Blo 1156638 3766925 := bstep (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) B1412597
theorem B1735313 : Blo 1156638 1735313 := bstep (se 2 (by rfl) ⟨650742, by rfl⟩ : syracuseStep 1735313 = 1301485) B1301485
theorem B1735331 : Blo 1156638 1735331 := bstep (se 1 (by rfl) ⟨1301498, by rfl⟩ : syracuseStep 1735331 = 2602997) B2602997
theorem B1735361 : Blo 1156638 1735361 := bstep (se 2 (by rfl) ⟨650760, by rfl⟩ : syracuseStep 1735361 = 1301521) B1301521
theorem B1735379 : Blo 1156638 1735379 := bstep (se 1 (by rfl) ⟨1301534, by rfl⟩ : syracuseStep 1735379 = 2603069) B2603069
theorem B1735409 : Blo 1156638 1735409 := bstep (se 2 (by rfl) ⟨650778, by rfl⟩ : syracuseStep 1735409 = 1301557) B1301557
theorem B1735427 : Blo 1156638 1735427 := bstep (se 1 (by rfl) ⟨1301570, by rfl⟩ : syracuseStep 1735427 = 2603141) B2603141
theorem B1735457 : Blo 1156638 1735457 := bstep (se 2 (by rfl) ⟨650796, by rfl⟩ : syracuseStep 1735457 = 1301593) B1301593
theorem B1735475 : Blo 1156638 1735475 := bstep (se 1 (by rfl) ⟨1301606, by rfl⟩ : syracuseStep 1735475 = 2603213) B2603213
theorem B1735505 : Blo 1156638 1735505 := bstep (se 2 (by rfl) ⟨650814, by rfl⟩ : syracuseStep 1735505 = 1301629) B1301629
theorem B1735523 : Blo 1156638 1735523 := bstep (se 1 (by rfl) ⟨1301642, by rfl⟩ : syracuseStep 1735523 = 2603285) B2603285
theorem B1735553 : Blo 1156638 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1735571 : Blo 1156638 1735571 := bstep (se 1 (by rfl) ⟨1301678, by rfl⟩ : syracuseStep 1735571 = 2603357) B2603357
theorem B1735601 : Blo 1156638 1735601 := bstep (se 2 (by rfl) ⟨650850, by rfl⟩ : syracuseStep 1735601 = 1301701) B1301701
theorem B1735619 : Blo 1156638 1735619 := bstep (se 1 (by rfl) ⟨1301714, by rfl⟩ : syracuseStep 1735619 = 2603429) B2603429
theorem B1735649 : Blo 1156638 1735649 := bstep (se 2 (by rfl) ⟨650868, by rfl⟩ : syracuseStep 1735649 = 1301737) B1301737
theorem B1735667 : Blo 1156638 1735667 := bstep (se 1 (by rfl) ⟨1301750, by rfl⟩ : syracuseStep 1735667 = 2603501) B2603501
theorem B1735697 : Blo 1156638 1735697 := bstep (se 2 (by rfl) ⟨650886, by rfl⟩ : syracuseStep 1735697 = 1301773) B1301773
theorem B1735715 : Blo 1156638 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B1735745 : Blo 1156638 1735745 := bstep (se 2 (by rfl) ⟨650904, by rfl⟩ : syracuseStep 1735745 = 1301809) B1301809
theorem B1735763 : Blo 1156638 1735763 := bstep (se 1 (by rfl) ⟨1301822, by rfl⟩ : syracuseStep 1735763 = 2603645) B2603645
theorem B1735793 : Blo 1156638 1735793 := bstep (se 2 (by rfl) ⟨650922, by rfl⟩ : syracuseStep 1735793 = 1301845) B1301845
theorem B5864561 : Blo 1156638 5864561 := bstep (se 2 (by rfl) ⟨2199210, by rfl⟩ : syracuseStep 5864561 = 4398421) B4398421
theorem B1735811 : Blo 1156638 1735811 := bstep (se 1 (by rfl) ⟨1301858, by rfl⟩ : syracuseStep 1735811 = 2603717) B2603717
theorem B1735841 : Blo 1156638 1735841 := bstep (se 2 (by rfl) ⟨650940, by rfl⟩ : syracuseStep 1735841 = 1301881) B1301881
theorem B1735859 : Blo 1156638 1735859 := bstep (se 1 (by rfl) ⟨1301894, by rfl⟩ : syracuseStep 1735859 = 2603789) B2603789
theorem B1735889 : Blo 1156638 1735889 := bstep (se 2 (by rfl) ⟨650958, by rfl⟩ : syracuseStep 1735889 = 1301917) B1301917
theorem B1735907 : Blo 1156638 1735907 := bstep (se 1 (by rfl) ⟨1301930, by rfl⟩ : syracuseStep 1735907 = 2603861) B2603861
theorem B1735937 : Blo 1156638 1735937 := bstep (se 2 (by rfl) ⟨650976, by rfl⟩ : syracuseStep 1735937 = 1301953) B1301953
theorem B1735955 : Blo 1156638 1735955 := bstep (se 1 (by rfl) ⟨1301966, by rfl⟩ : syracuseStep 1735955 = 2603933) B2603933
theorem B1735985 : Blo 1156638 1735985 := bstep (se 2 (by rfl) ⟨650994, by rfl⟩ : syracuseStep 1735985 = 1301989) B1301989
theorem B1736003 : Blo 1156638 1736003 := bstep (se 1 (by rfl) ⟨1302002, by rfl⟩ : syracuseStep 1736003 = 2604005) B2604005
theorem B1736033 : Blo 1156638 1736033 := bstep (se 2 (by rfl) ⟨651012, by rfl⟩ : syracuseStep 1736033 = 1302025) B1302025
theorem B1736051 : Blo 1156638 1736051 := bstep (se 1 (by rfl) ⟨1302038, by rfl⟩ : syracuseStep 1736051 = 2604077) B2604077
theorem B1736081 : Blo 1156638 1736081 := bstep (se 2 (by rfl) ⟨651030, by rfl⟩ : syracuseStep 1736081 = 1302061) B1302061
theorem B1736099 : Blo 1156638 1736099 := bstep (se 1 (by rfl) ⟨1302074, by rfl⟩ : syracuseStep 1736099 = 2604149) B2604149
theorem B1736129 : Blo 1156638 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B1736147 : Blo 1156638 1736147 := bstep (se 1 (by rfl) ⟨1302110, by rfl⟩ : syracuseStep 1736147 = 2604221) B2604221
theorem B1736177 : Blo 1156638 1736177 := bstep (se 2 (by rfl) ⟨651066, by rfl⟩ : syracuseStep 1736177 = 1302133) B1302133
theorem B1736195 : Blo 1156638 1736195 := bstep (se 1 (by rfl) ⟨1302146, by rfl⟩ : syracuseStep 1736195 = 2604293) B2604293
theorem B1736225 : Blo 1156638 1736225 := bstep (se 2 (by rfl) ⟨651084, by rfl⟩ : syracuseStep 1736225 = 1302169) B1302169
theorem B1736243 : Blo 1156638 1736243 := bstep (se 1 (by rfl) ⟨1302182, by rfl⟩ : syracuseStep 1736243 = 2604365) B2604365
theorem B1736273 : Blo 1156638 1736273 := bstep (se 2 (by rfl) ⟨651102, by rfl⟩ : syracuseStep 1736273 = 1302205) B1302205
theorem B1736291 : Blo 1156638 1736291 := bstep (se 1 (by rfl) ⟨1302218, by rfl⟩ : syracuseStep 1736291 = 2604437) B2604437
theorem B13205105 : Blo 1156638 13205105 := bstep (se 2 (by rfl) ⟨4951914, by rfl⟩ : syracuseStep 13205105 = 9903829) B9903829
theorem B1736321 : Blo 1156638 1736321 := bstep (se 2 (by rfl) ⟨651120, by rfl⟩ : syracuseStep 1736321 = 1302241) B1302241
theorem B1736339 : Blo 1156638 1736339 := bstep (se 1 (by rfl) ⟨1302254, by rfl⟩ : syracuseStep 1736339 = 2604509) B2604509
theorem B1736369 : Blo 1156638 1736369 := bstep (se 2 (by rfl) ⟨651138, by rfl⟩ : syracuseStep 1736369 = 1302277) B1302277
theorem B1736387 : Blo 1156638 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B1736417 : Blo 1156638 1736417 := bstep (se 2 (by rfl) ⟨651156, by rfl⟩ : syracuseStep 1736417 = 1302313) B1302313
theorem B1736435 : Blo 1156638 1736435 := bstep (se 1 (by rfl) ⟨1302326, by rfl⟩ : syracuseStep 1736435 = 2604653) B2604653
theorem B1736465 : Blo 1156638 1736465 := bstep (se 2 (by rfl) ⟨651174, by rfl⟩ : syracuseStep 1736465 = 1302349) B1302349
theorem B1736483 : Blo 1156638 1736483 := bstep (se 1 (by rfl) ⟨1302362, by rfl⟩ : syracuseStep 1736483 = 2604725) B2604725
theorem B1736513 : Blo 1156638 1736513 := bstep (se 2 (by rfl) ⟨651192, by rfl⟩ : syracuseStep 1736513 = 1302385) B1302385
theorem B1736531 : Blo 1156638 1736531 := bstep (se 1 (by rfl) ⟨1302398, by rfl⟩ : syracuseStep 1736531 = 2604797) B2604797
theorem B1736561 : Blo 1156638 1736561 := bstep (se 2 (by rfl) ⟨651210, by rfl⟩ : syracuseStep 1736561 = 1302421) B1302421
theorem B1736579 : Blo 1156638 1736579 := bstep (se 1 (by rfl) ⟨1302434, by rfl⟩ : syracuseStep 1736579 = 2604869) B2604869
theorem B1736609 : Blo 1156638 1736609 := bstep (se 2 (by rfl) ⟨651228, by rfl⟩ : syracuseStep 1736609 = 1302457) B1302457
theorem B1736627 : Blo 1156638 1736627 := bstep (se 1 (by rfl) ⟨1302470, by rfl⟩ : syracuseStep 1736627 = 2604941) B2604941
theorem B1736657 : Blo 1156638 1736657 := bstep (se 2 (by rfl) ⟨651246, by rfl⟩ : syracuseStep 1736657 = 1302493) B1302493
theorem B1736675 : Blo 1156638 1736675 := bstep (se 1 (by rfl) ⟨1302506, by rfl⟩ : syracuseStep 1736675 = 2605013) B2605013
theorem B1736729 : Blo 1156638 1736729 := bstep (se 2 (by rfl) ⟨651273, by rfl⟩ : syracuseStep 1736729 = 1302547) B1302547
theorem B1736843 : Blo 1156638 1736843 := bstep (se 1 (by rfl) ⟨1302632, by rfl⟩ : syracuseStep 1736843 = 2605265) B2605265
theorem B1736855 : Blo 1156638 1736855 := bstep (se 1 (by rfl) ⟨1302641, by rfl⟩ : syracuseStep 1736855 = 2605283) B2605283
theorem B1736921 : Blo 1156638 1736921 := bstep (se 2 (by rfl) ⟨651345, by rfl⟩ : syracuseStep 1736921 = 1302691) B1302691
theorem B1737035 : Blo 1156638 1737035 := bstep (se 1 (by rfl) ⟨1302776, by rfl⟩ : syracuseStep 1737035 = 2605553) B2605553
theorem B1737047 : Blo 1156638 1737047 := bstep (se 1 (by rfl) ⟨1302785, by rfl⟩ : syracuseStep 1737047 = 2605571) B2605571
theorem B1737113 : Blo 1156638 1737113 := bstep (se 2 (by rfl) ⟨651417, by rfl⟩ : syracuseStep 1737113 = 1302835) B1302835
theorem B4948397 : Blo 1156638 4948397 := bstep (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) B1855649
theorem B1737227 : Blo 1156638 1737227 := bstep (se 1 (by rfl) ⟨1302920, by rfl⟩ : syracuseStep 1737227 = 2605841) B2605841
theorem B1737239 : Blo 1156638 1737239 := bstep (se 1 (by rfl) ⟨1302929, by rfl⟩ : syracuseStep 1737239 = 2605859) B2605859
theorem B6685249 : Blo 1156638 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B1737305 : Blo 1156638 1737305 := bstep (se 2 (by rfl) ⟨651489, by rfl⟩ : syracuseStep 1737305 = 1302979) B1302979
theorem B4391617 : Blo 1156638 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B1737419 : Blo 1156638 1737419 := bstep (se 1 (by rfl) ⟨1303064, by rfl⟩ : syracuseStep 1737419 = 2606129) B2606129
theorem B1737431 : Blo 1156638 1737431 := bstep (se 1 (by rfl) ⟨1303073, by rfl⟩ : syracuseStep 1737431 = 2606147) B2606147
theorem B29721329 : Blo 1156638 29721329 := bstep (se 2 (by rfl) ⟨11145498, by rfl⟩ : syracuseStep 29721329 = 22290997) B22290997
theorem B1671959 : Blo 1156638 1671959 := bstep (se 1 (by rfl) ⟨1253969, by rfl⟩ : syracuseStep 1671959 = 2507939) B2507939
theorem B1737497 : Blo 1156638 1737497 := bstep (se 2 (by rfl) ⟨651561, by rfl⟩ : syracuseStep 1737497 = 1303123) B1303123
theorem B4457267 : Blo 1156638 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B1737611 : Blo 1156638 1737611 := bstep (se 1 (by rfl) ⟨1303208, by rfl⟩ : syracuseStep 1737611 = 2606417) B2606417
theorem B1737623 : Blo 1156638 1737623 := bstep (se 1 (by rfl) ⟨1303217, by rfl⟩ : syracuseStep 1737623 = 2606435) B2606435
theorem B1737689 : Blo 1156638 1737689 := bstep (se 2 (by rfl) ⟨651633, by rfl⟩ : syracuseStep 1737689 = 1303267) B1303267
theorem B13206563 : Blo 1156638 13206563 := bstep (se 1 (by rfl) ⟨9904922, by rfl⟩ : syracuseStep 13206563 = 19809845) B19809845
theorem B1737803 : Blo 1156638 1737803 := bstep (se 1 (by rfl) ⟨1303352, by rfl⟩ : syracuseStep 1737803 = 2606705) B2606705
theorem B1737815 : Blo 1156638 1737815 := bstep (se 1 (by rfl) ⟨1303361, by rfl⟩ : syracuseStep 1737815 = 2606723) B2606723
theorem B1737881 : Blo 1156638 1737881 := bstep (se 2 (by rfl) ⟨651705, by rfl⟩ : syracuseStep 1737881 = 1303411) B1303411
theorem B2196659 : Blo 1156638 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B1737995 : Blo 1156638 1737995 := bstep (se 1 (by rfl) ⟨1303496, by rfl⟩ : syracuseStep 1737995 = 2606993) B2606993
theorem B1738007 : Blo 1156638 1738007 := bstep (se 1 (by rfl) ⟨1303505, by rfl⟩ : syracuseStep 1738007 = 2607011) B2607011
theorem B8357165 : Blo 1156638 8357165 := bstep (se 3 (by rfl) ⟨1566968, by rfl⟩ : syracuseStep 8357165 = 3133937) B3133937
theorem B2196811 : Blo 1156638 2196811 := bstep (se 1 (by rfl) ⟨1647608, by rfl⟩ : syracuseStep 2196811 = 3295217) B3295217
theorem B1738073 : Blo 1156638 1738073 := bstep (se 2 (by rfl) ⟨651777, by rfl⟩ : syracuseStep 1738073 = 1303555) B1303555
theorem B1738187 : Blo 1156638 1738187 := bstep (se 1 (by rfl) ⟨1303640, by rfl⟩ : syracuseStep 1738187 = 2607281) B2607281
theorem B1738199 : Blo 1156638 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B1738265 : Blo 1156638 1738265 := bstep (se 2 (by rfl) ⟨651849, by rfl⟩ : syracuseStep 1738265 = 1303699) B1303699
theorem B1738379 : Blo 1156638 1738379 := bstep (se 1 (by rfl) ⟨1303784, by rfl⟩ : syracuseStep 1738379 = 2607569) B2607569
theorem B1738391 : Blo 1156638 1738391 := bstep (se 1 (by rfl) ⟨1303793, by rfl⟩ : syracuseStep 1738391 = 2607587) B2607587
theorem B2197145 : Blo 1156638 2197145 := bstep (se 2 (by rfl) ⟨823929, by rfl⟩ : syracuseStep 2197145 = 1647859) B1647859
theorem B1738457 : Blo 1156638 1738457 := bstep (se 2 (by rfl) ⟨651921, by rfl⟩ : syracuseStep 1738457 = 1303843) B1303843
theorem B18810629 : Blo 1156638 18810629 := bstep (se 4 (by rfl) ⟨1763496, by rfl⟩ : syracuseStep 18810629 = 3526993) B3526993
theorem B1738571 : Blo 1156638 1738571 := bstep (se 1 (by rfl) ⟨1303928, by rfl⟩ : syracuseStep 1738571 = 2607857) B2607857
theorem B1738583 : Blo 1156638 1738583 := bstep (se 1 (by rfl) ⟨1303937, by rfl⟩ : syracuseStep 1738583 = 2607875) B2607875
theorem B4949849 : Blo 1156638 4949849 := bstep (se 2 (by rfl) ⟨1856193, by rfl⟩ : syracuseStep 4949849 = 3712387) B3712387
theorem B53446499 : Blo 1156638 53446499 := bstep (se 1 (by rfl) ⟨40084874, by rfl⟩ : syracuseStep 53446499 = 80169749) B80169749
theorem B1738649 : Blo 1156638 1738649 := bstep (se 2 (by rfl) ⟨651993, by rfl⟩ : syracuseStep 1738649 = 1303987) B1303987
theorem B2230195 : Blo 1156638 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B1738763 : Blo 1156638 1738763 := bstep (se 1 (by rfl) ⟨1304072, by rfl⟩ : syracuseStep 1738763 = 2608145) B2608145
theorem B1738775 : Blo 1156638 1738775 := bstep (se 1 (by rfl) ⟨1304081, by rfl⟩ : syracuseStep 1738775 = 2608163) B2608163
theorem B1738841 : Blo 1156638 1738841 := bstep (se 2 (by rfl) ⟨652065, by rfl⟩ : syracuseStep 1738841 = 1304131) B1304131
theorem B2230465 : Blo 1156638 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B1738955 : Blo 1156638 1738955 := bstep (se 1 (by rfl) ⟨1304216, by rfl⟩ : syracuseStep 1738955 = 2608433) B2608433
theorem B1738967 : Blo 1156638 1738967 := bstep (se 1 (by rfl) ⟨1304225, by rfl⟩ : syracuseStep 1738967 = 2608451) B2608451
theorem B2197783 : Blo 1156638 2197783 := bstep (se 1 (by rfl) ⟨1648337, by rfl⟩ : syracuseStep 2197783 = 3296675) B3296675
theorem B1739033 : Blo 1156638 1739033 := bstep (se 2 (by rfl) ⟨652137, by rfl⟩ : syracuseStep 1739033 = 1304275) B1304275
theorem B1739147 : Blo 1156638 1739147 := bstep (se 1 (by rfl) ⟨1304360, by rfl⟩ : syracuseStep 1739147 = 2608721) B2608721
theorem B1739159 : Blo 1156638 1739159 := bstep (se 1 (by rfl) ⟨1304369, by rfl⟩ : syracuseStep 1739159 = 2608739) B2608739
theorem B1739225 : Blo 1156638 1739225 := bstep (se 2 (by rfl) ⟨652209, by rfl⟩ : syracuseStep 1739225 = 1304419) B1304419
theorem B9406937 : Blo 1156638 9406937 := bstep (se 2 (by rfl) ⟨3527601, by rfl⟩ : syracuseStep 9406937 = 7055203) B7055203
theorem B8784449 : Blo 1156638 8784449 := bstep (se 2 (by rfl) ⟨3294168, by rfl⟩ : syracuseStep 8784449 = 6588337) B6588337
theorem B4393547 : Blo 1156638 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B1739339 : Blo 1156638 1739339 := bstep (se 1 (by rfl) ⟨1304504, by rfl⟩ : syracuseStep 1739339 = 2609009) B2609009
theorem B5573195 : Blo 1156638 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B1739351 : Blo 1156638 1739351 := bstep (se 1 (by rfl) ⟨1304513, by rfl⟩ : syracuseStep 1739351 = 2609027) B2609027
theorem B4393561 : Blo 1156638 4393561 := bstep (se 2 (by rfl) ⟨1647585, by rfl⟩ : syracuseStep 4393561 = 3295171) B3295171
theorem B5868125 : Blo 1156638 5868125 := bstep (se 3 (by rfl) ⟨1100273, by rfl⟩ : syracuseStep 5868125 = 2200547) B2200547
theorem B1739417 : Blo 1156638 1739417 := bstep (se 2 (by rfl) ⟨652281, by rfl⟩ : syracuseStep 1739417 = 1304563) B1304563
theorem B1739531 : Blo 1156638 1739531 := bstep (se 1 (by rfl) ⟨1304648, by rfl⟩ : syracuseStep 1739531 = 2609297) B2609297
theorem B1739543 : Blo 1156638 1739543 := bstep (se 1 (by rfl) ⟨1304657, by rfl⟩ : syracuseStep 1739543 = 2609315) B2609315
theorem B1739609 : Blo 1156638 1739609 := bstep (se 2 (by rfl) ⟨652353, by rfl⟩ : syracuseStep 1739609 = 1304707) B1304707
theorem B2821043 : Blo 1156638 2821043 := bstep (se 1 (by rfl) ⟨2115782, by rfl⟩ : syracuseStep 2821043 = 4231565) B4231565
theorem B1739723 : Blo 1156638 1739723 := bstep (se 1 (by rfl) ⟨1304792, by rfl⟩ : syracuseStep 1739723 = 2609585) B2609585
theorem B1739735 : Blo 1156638 1739735 := bstep (se 1 (by rfl) ⟨1304801, by rfl⟩ : syracuseStep 1739735 = 2609603) B2609603
theorem B33852377 : Blo 1156638 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B10030085 : Blo 1156638 10030085 := bstep (se 4 (by rfl) ⟨940320, by rfl⟩ : syracuseStep 10030085 = 1880641) B1880641
theorem B1739801 : Blo 1156638 1739801 := bstep (se 2 (by rfl) ⟨652425, by rfl⟩ : syracuseStep 1739801 = 1304851) B1304851
theorem B2198603 : Blo 1156638 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B2198657 : Blo 1156638 2198657 := bstep (se 2 (by rfl) ⟨824496, by rfl⟩ : syracuseStep 2198657 = 1648993) B1648993
theorem B1739915 : Blo 1156638 1739915 := bstep (se 1 (by rfl) ⟨1304936, by rfl⟩ : syracuseStep 1739915 = 2609873) B2609873
theorem B1739927 : Blo 1156638 1739927 := bstep (se 1 (by rfl) ⟨1304945, by rfl⟩ : syracuseStep 1739927 = 2609891) B2609891
theorem B2231489 : Blo 1156638 2231489 := bstep (se 2 (by rfl) ⟨836808, by rfl⟩ : syracuseStep 2231489 = 1673617) B1673617
theorem B1739993 : Blo 1156638 1739993 := bstep (se 2 (by rfl) ⟨652497, by rfl⟩ : syracuseStep 1739993 = 1304995) B1304995
theorem B1740107 : Blo 1156638 1740107 := bstep (se 1 (by rfl) ⟨1305080, by rfl⟩ : syracuseStep 1740107 = 2610161) B2610161
theorem B1740119 : Blo 1156638 1740119 := bstep (se 1 (by rfl) ⟨1305089, by rfl⟩ : syracuseStep 1740119 = 2610179) B2610179
theorem B1740185 : Blo 1156638 1740185 := bstep (se 2 (by rfl) ⟨652569, by rfl⟩ : syracuseStep 1740185 = 1305139) B1305139
theorem B4951489 : Blo 1156638 4951489 := bstep (se 2 (by rfl) ⟨1856808, by rfl⟩ : syracuseStep 4951489 = 3713617) B3713617
theorem B1740299 : Blo 1156638 1740299 := bstep (se 1 (by rfl) ⟨1305224, by rfl⟩ : syracuseStep 1740299 = 2610449) B2610449
theorem B4394519 : Blo 1156638 4394519 := bstep (se 1 (by rfl) ⟨3295889, by rfl⟩ : syracuseStep 4394519 = 6591779) B6591779
theorem B1740311 : Blo 1156638 1740311 := bstep (se 1 (by rfl) ⟨1305233, by rfl⟩ : syracuseStep 1740311 = 2610467) B2610467
theorem B1740377 : Blo 1156638 1740377 := bstep (se 2 (by rfl) ⟨652641, by rfl⟩ : syracuseStep 1740377 = 1305283) B1305283
theorem B1740491 : Blo 1156638 1740491 := bstep (se 1 (by rfl) ⟨1305368, by rfl⟩ : syracuseStep 1740491 = 2610737) B2610737
theorem B1740503 : Blo 1156638 1740503 := bstep (se 1 (by rfl) ⟨1305377, by rfl⟩ : syracuseStep 1740503 = 2610755) B2610755
theorem B1740569 : Blo 1156638 1740569 := bstep (se 2 (by rfl) ⟨652713, by rfl⟩ : syracuseStep 1740569 = 1305427) B1305427
theorem B1740683 : Blo 1156638 1740683 := bstep (se 1 (by rfl) ⟨1305512, by rfl⟩ : syracuseStep 1740683 = 2611025) B2611025
theorem B1740695 : Blo 1156638 1740695 := bstep (se 1 (by rfl) ⟨1305521, by rfl⟩ : syracuseStep 1740695 = 2611043) B2611043
theorem B1740761 : Blo 1156638 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B2199575 : Blo 1156638 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B4952087 : Blo 1156638 4952087 := bstep (se 1 (by rfl) ⟨3714065, by rfl⟩ : syracuseStep 4952087 = 7428131) B7428131
theorem B3706955 : Blo 1156638 3706955 := bstep (se 1 (by rfl) ⟨2780216, by rfl⟩ : syracuseStep 3706955 = 5560433) B5560433
theorem B1740875 : Blo 1156638 1740875 := bstep (se 1 (by rfl) ⟨1305656, by rfl⟩ : syracuseStep 1740875 = 2611313) B2611313
theorem B1740887 : Blo 1156638 1740887 := bstep (se 1 (by rfl) ⟨1305665, by rfl⟩ : syracuseStep 1740887 = 2611331) B2611331
theorem B11145347 : Blo 1156638 11145347 := bstep (se 1 (by rfl) ⟨8359010, by rfl⟩ : syracuseStep 11145347 = 16718021) B16718021
theorem B25071767 : Blo 1156638 25071767 := bstep (se 1 (by rfl) ⟨18803825, by rfl⟩ : syracuseStep 25071767 = 37607651) B37607651
theorem B1740953 : Blo 1156638 1740953 := bstep (se 2 (by rfl) ⟨652857, by rfl⟩ : syracuseStep 1740953 = 1305715) B1305715
theorem B3903767 : Blo 1156638 3903767 := bstep (se 1 (by rfl) ⟨2927825, by rfl⟩ : syracuseStep 3903767 = 5855651) B5855651
theorem B2232665 : Blo 1156638 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B9408919 : Blo 1156638 9408919 := bstep (se 1 (by rfl) ⟨7056689, by rfl⟩ : syracuseStep 9408919 = 14113379) B14113379
theorem B8786393 : Blo 1156638 8786393 := bstep (se 2 (by rfl) ⟨3294897, by rfl⟩ : syracuseStep 8786393 = 6589795) B6589795
theorem B2200115 : Blo 1156638 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B5870231 : Blo 1156638 5870231 := bstep (se 1 (by rfl) ⟨4402673, by rfl⟩ : syracuseStep 5870231 = 8805347) B8805347
theorem B4395779 : Blo 1156638 4395779 := bstep (se 1 (by rfl) ⟨3296834, by rfl⟩ : syracuseStep 4395779 = 6593669) B6593669
theorem B3904307 : Blo 1156638 3904307 := bstep (se 1 (by rfl) ⟨2928230, by rfl⟩ : syracuseStep 3904307 = 5856461) B5856461
theorem B2200601 : Blo 1156638 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B3904577 : Blo 1156638 3904577 := bstep (se 2 (by rfl) ⟨1464216, by rfl⟩ : syracuseStep 3904577 = 2928433) B2928433
theorem B7050341 : Blo 1156638 7050341 := bstep (se 4 (by rfl) ⟨660969, by rfl⟩ : syracuseStep 7050341 = 1321939) B1321939
theorem B16094339 : Blo 1156638 16094339 := bstep (se 1 (by rfl) ⟨12070754, by rfl⟩ : syracuseStep 16094339 = 24141509) B24141509
theorem B4953419 : Blo 1156638 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B9410053 : Blo 1156638 9410053 := bstep (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) B1764385
theorem B3905117 : Blo 1156638 3905117 := bstep (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) B1464419
theorem B3348119 : Blo 1156638 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B16684805 : Blo 1156638 16684805 := bstep (se 4 (by rfl) ⟨1564200, by rfl⟩ : syracuseStep 16684805 = 3128401) B3128401
theorem B5085149 : Blo 1156638 5085149 := bstep (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) B1906931
theorem B6592529 : Blo 1156638 6592529 := bstep (se 2 (by rfl) ⟨2472198, by rfl⟩ : syracuseStep 6592529 = 4944397) B4944397
theorem B3709145 : Blo 1156638 3709145 := bstep (se 2 (by rfl) ⟨1390929, by rfl⟩ : syracuseStep 3709145 = 2781859) B2781859
theorem B7411985 : Blo 1156638 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B3709273 : Blo 1156638 3709273 := bstep (se 2 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 3709273 = 2781955) B2781955
theorem B4954547 : Blo 1156638 4954547 := bstep (se 1 (by rfl) ⟨3715910, by rfl⟩ : syracuseStep 4954547 = 7431821) B7431821
theorem B2202059 : Blo 1156638 2202059 := bstep (se 1 (by rfl) ⟨1651544, by rfl⟩ : syracuseStep 2202059 = 3303089) B3303089
theorem B6592985 : Blo 1156638 6592985 := bstep (se 2 (by rfl) ⟨2472369, by rfl⟩ : syracuseStep 6592985 = 4944739) B4944739
theorem B3709529 : Blo 1156638 3709529 := bstep (se 2 (by rfl) ⟨1391073, by rfl⟩ : syracuseStep 3709529 = 2782147) B2782147
theorem B2202241 : Blo 1156638 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B3906251 : Blo 1156638 3906251 := bstep (se 1 (by rfl) ⟨2929688, by rfl⟩ : syracuseStep 3906251 = 5859377) B5859377
theorem B3906521 : Blo 1156638 3906521 := bstep (se 2 (by rfl) ⟨1464945, by rfl⟩ : syracuseStep 3906521 = 2929891) B2929891
theorem B5348317 : Blo 1156638 5348317 := bstep (se 3 (by rfl) ⟨1002809, by rfl⟩ : syracuseStep 5348317 = 2005619) B2005619
theorem B2202689 : Blo 1156638 2202689 := bstep (se 2 (by rfl) ⟨826008, by rfl⟩ : syracuseStep 2202689 = 1652017) B1652017
theorem B4463837 : Blo 1156638 4463837 := bstep (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) B1673939
theorem B2203031 : Blo 1156638 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B3907223 : Blo 1156638 3907223 := bstep (se 1 (by rfl) ⟨2930417, by rfl⟩ : syracuseStep 3907223 = 5860835) B5860835
theorem B2006731 : Blo 1156638 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B8789795 : Blo 1156638 8789795 := bstep (se 1 (by rfl) ⟨6592346, by rfl⟩ : syracuseStep 8789795 = 13184693) B13184693
theorem B4398893 : Blo 1156638 4398893 := bstep (se 3 (by rfl) ⟨824792, by rfl⟩ : syracuseStep 4398893 = 1649585) B1649585
theorem B3710785 : Blo 1156638 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B4464715 : Blo 1156638 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B5873795 : Blo 1156638 5873795 := bstep (se 1 (by rfl) ⟨4405346, by rfl⟩ : syracuseStep 5873795 = 8810693) B8810693
theorem B3907763 : Blo 1156638 3907763 := bstep (se 1 (by rfl) ⟨2930822, by rfl⟩ : syracuseStep 3907763 = 5861645) B5861645
theorem B4235485 : Blo 1156638 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B4956461 : Blo 1156638 4956461 := bstep (se 3 (by rfl) ⟨929336, by rfl⟩ : syracuseStep 4956461 = 1858673) B1858673
theorem B3908033 : Blo 1156638 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B4399667 : Blo 1156638 4399667 := bstep (se 1 (by rfl) ⟨3299750, by rfl⟩ : syracuseStep 4399667 = 6599501) B6599501
theorem B1647307 : Blo 1156638 1647307 := bstep (se 1 (by rfl) ⟨1235480, by rfl⟩ : syracuseStep 1647307 = 2470961) B2470961
theorem B8364865 : Blo 1156638 8364865 := bstep (se 2 (by rfl) ⟨3136824, by rfl⟩ : syracuseStep 8364865 = 6273649) B6273649
theorem B7054181 : Blo 1156638 7054181 := bstep (se 4 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 7054181 = 1322659) B1322659
theorem B4957145 : Blo 1156638 4957145 := bstep (se 2 (by rfl) ⟨1858929, by rfl⟩ : syracuseStep 4957145 = 3717859) B3717859
theorem B3908573 : Blo 1156638 3908573 := bstep (se 3 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 3908573 = 1465715) B1465715
theorem B33367301 : Blo 1156638 33367301 := bstep (se 4 (by rfl) ⟨3128184, by rfl⟩ : syracuseStep 33367301 = 6256369) B6256369
theorem B11150693 : Blo 1156638 11150693 := bstep (se 4 (by rfl) ⟨1045377, by rfl⟩ : syracuseStep 11150693 = 2090755) B2090755
theorem B1156651 : Blo 1156638 1156651 := bstep (se 1 (by rfl) ⟨867488, by rfl⟩ : syracuseStep 1156651 = 1734977) B1734977
theorem B1156663 : Blo 1156638 1156663 := bstep (se 1 (by rfl) ⟨867497, by rfl⟩ : syracuseStep 1156663 = 1734995) B1734995
theorem B1156683 : Blo 1156638 1156683 := bstep (se 1 (by rfl) ⟨867512, by rfl⟩ : syracuseStep 1156683 = 1735025) B1735025
theorem B1156695 : Blo 1156638 1156695 := bstep (se 1 (by rfl) ⟨867521, by rfl⟩ : syracuseStep 1156695 = 1735043) B1735043
theorem B1156715 : Blo 1156638 1156715 := bstep (se 1 (by rfl) ⟨867536, by rfl⟩ : syracuseStep 1156715 = 1735073) B1735073
theorem B1156727 : Blo 1156638 1156727 := bstep (se 1 (by rfl) ⟨867545, by rfl⟩ : syracuseStep 1156727 = 1735091) B1735091
theorem B1156747 : Blo 1156638 1156747 := bstep (se 1 (by rfl) ⟨867560, by rfl⟩ : syracuseStep 1156747 = 1735121) B1735121
theorem B1156759 : Blo 1156638 1156759 := bstep (se 1 (by rfl) ⟨867569, by rfl⟩ : syracuseStep 1156759 = 1735139) B1735139
theorem B1156779 : Blo 1156638 1156779 := bstep (se 1 (by rfl) ⟨867584, by rfl⟩ : syracuseStep 1156779 = 1735169) B1735169
theorem B10725043 : Blo 1156638 10725043 := bstep (se 1 (by rfl) ⟨8043782, by rfl⟩ : syracuseStep 10725043 = 16087565) B16087565
theorem B1156791 : Blo 1156638 1156791 := bstep (se 1 (by rfl) ⟨867593, by rfl⟩ : syracuseStep 1156791 = 1735187) B1735187
theorem B1156811 : Blo 1156638 1156811 := bstep (se 1 (by rfl) ⟨867608, by rfl⟩ : syracuseStep 1156811 = 1735217) B1735217
theorem B1156823 : Blo 1156638 1156823 := bstep (se 1 (by rfl) ⟨867617, by rfl⟩ : syracuseStep 1156823 = 1735235) B1735235
theorem B1156843 : Blo 1156638 1156843 := bstep (se 1 (by rfl) ⟨867632, by rfl⟩ : syracuseStep 1156843 = 1735265) B1735265
theorem B1156855 : Blo 1156638 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B1156875 : Blo 1156638 1156875 := bstep (se 1 (by rfl) ⟨867656, by rfl⟩ : syracuseStep 1156875 = 1735313) B1735313
theorem B1156887 : Blo 1156638 1156887 := bstep (se 1 (by rfl) ⟨867665, by rfl⟩ : syracuseStep 1156887 = 1735331) B1735331
theorem B1156907 : Blo 1156638 1156907 := bstep (se 1 (by rfl) ⟨867680, by rfl⟩ : syracuseStep 1156907 = 1735361) B1735361
theorem B1156919 : Blo 1156638 1156919 := bstep (se 1 (by rfl) ⟨867689, by rfl⟩ : syracuseStep 1156919 = 1735379) B1735379
theorem B1156939 : Blo 1156638 1156939 := bstep (se 1 (by rfl) ⟨867704, by rfl⟩ : syracuseStep 1156939 = 1735409) B1735409
theorem B1156951 : Blo 1156638 1156951 := bstep (se 1 (by rfl) ⟨867713, by rfl⟩ : syracuseStep 1156951 = 1735427) B1735427
theorem B1156971 : Blo 1156638 1156971 := bstep (se 1 (by rfl) ⟨867728, by rfl⟩ : syracuseStep 1156971 = 1735457) B1735457
theorem B1156983 : Blo 1156638 1156983 := bstep (se 1 (by rfl) ⟨867737, by rfl⟩ : syracuseStep 1156983 = 1735475) B1735475
theorem B1157003 : Blo 1156638 1157003 := bstep (se 1 (by rfl) ⟨867752, by rfl⟩ : syracuseStep 1157003 = 1735505) B1735505
theorem B1157015 : Blo 1156638 1157015 := bstep (se 1 (by rfl) ⟨867761, by rfl⟩ : syracuseStep 1157015 = 1735523) B1735523
theorem B1157035 : Blo 1156638 1157035 := bstep (se 1 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 1157035 = 1735553) B1735553
theorem B1157047 : Blo 1156638 1157047 := bstep (se 1 (by rfl) ⟨867785, by rfl⟩ : syracuseStep 1157047 = 1735571) B1735571
theorem B1157067 : Blo 1156638 1157067 := bstep (se 1 (by rfl) ⟨867800, by rfl⟩ : syracuseStep 1157067 = 1735601) B1735601
theorem B1157079 : Blo 1156638 1157079 := bstep (se 1 (by rfl) ⟨867809, by rfl⟩ : syracuseStep 1157079 = 1735619) B1735619
theorem B1157099 : Blo 1156638 1157099 := bstep (se 1 (by rfl) ⟨867824, by rfl⟩ : syracuseStep 1157099 = 1735649) B1735649
theorem B1157111 : Blo 1156638 1157111 := bstep (se 1 (by rfl) ⟨867833, by rfl⟩ : syracuseStep 1157111 = 1735667) B1735667
theorem B4401155 : Blo 1156638 4401155 := bstep (se 1 (by rfl) ⟨3300866, by rfl⟩ : syracuseStep 4401155 = 6601733) B6601733
theorem B1157131 : Blo 1156638 1157131 := bstep (se 1 (by rfl) ⟨867848, by rfl⟩ : syracuseStep 1157131 = 1735697) B1735697
theorem B1157143 : Blo 1156638 1157143 := bstep (se 1 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 1157143 = 1735715) B1735715
theorem B1157163 : Blo 1156638 1157163 := bstep (se 1 (by rfl) ⟨867872, by rfl⟩ : syracuseStep 1157163 = 1735745) B1735745
theorem B1157175 : Blo 1156638 1157175 := bstep (se 1 (by rfl) ⟨867881, by rfl⟩ : syracuseStep 1157175 = 1735763) B1735763
theorem B1157195 : Blo 1156638 1157195 := bstep (se 1 (by rfl) ⟨867896, by rfl⟩ : syracuseStep 1157195 = 1735793) B1735793
theorem B3909707 : Blo 1156638 3909707 := bstep (se 1 (by rfl) ⟨2932280, by rfl⟩ : syracuseStep 3909707 = 5864561) B5864561
theorem B1157207 : Blo 1156638 1157207 := bstep (se 1 (by rfl) ⟨867905, by rfl⟩ : syracuseStep 1157207 = 1735811) B1735811
theorem B4696157 : Blo 1156638 4696157 := bstep (se 3 (by rfl) ⟨880529, by rfl⟩ : syracuseStep 4696157 = 1761059) B1761059
theorem B1157227 : Blo 1156638 1157227 := bstep (se 1 (by rfl) ⟨867920, by rfl⟩ : syracuseStep 1157227 = 1735841) B1735841
theorem B1157239 : Blo 1156638 1157239 := bstep (se 1 (by rfl) ⟨867929, by rfl⟩ : syracuseStep 1157239 = 1735859) B1735859
theorem B1157259 : Blo 1156638 1157259 := bstep (se 1 (by rfl) ⟨867944, by rfl⟩ : syracuseStep 1157259 = 1735889) B1735889
theorem B1321099 : Blo 1156638 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B1157271 : Blo 1156638 1157271 := bstep (se 1 (by rfl) ⟨867953, by rfl⟩ : syracuseStep 1157271 = 1735907) B1735907
theorem B1648793 : Blo 1156638 1648793 := bstep (se 2 (by rfl) ⟨618297, by rfl⟩ : syracuseStep 1648793 = 1236595) B1236595
theorem B1157291 : Blo 1156638 1157291 := bstep (se 1 (by rfl) ⟨867968, by rfl⟩ : syracuseStep 1157291 = 1735937) B1735937
theorem B1157303 : Blo 1156638 1157303 := bstep (se 1 (by rfl) ⟨867977, by rfl⟩ : syracuseStep 1157303 = 1735955) B1735955
theorem B1157323 : Blo 1156638 1157323 := bstep (se 1 (by rfl) ⟨867992, by rfl⟩ : syracuseStep 1157323 = 1735985) B1735985
theorem B1157335 : Blo 1156638 1157335 := bstep (se 1 (by rfl) ⟨868001, by rfl⟩ : syracuseStep 1157335 = 1736003) B1736003
theorem B3811549 : Blo 1156638 3811549 := bstep (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) B1429331
theorem B1157355 : Blo 1156638 1157355 := bstep (se 1 (by rfl) ⟨868016, by rfl⟩ : syracuseStep 1157355 = 1736033) B1736033
theorem B16918769 : Blo 1156638 16918769 := bstep (se 2 (by rfl) ⟨6344538, by rfl⟩ : syracuseStep 16918769 = 12689077) B12689077
theorem B1157367 : Blo 1156638 1157367 := bstep (se 1 (by rfl) ⟨868025, by rfl⟩ : syracuseStep 1157367 = 1736051) B1736051
theorem B1157387 : Blo 1156638 1157387 := bstep (se 1 (by rfl) ⟨868040, by rfl⟩ : syracuseStep 1157387 = 1736081) B1736081
theorem B1157399 : Blo 1156638 1157399 := bstep (se 1 (by rfl) ⟨868049, by rfl⟩ : syracuseStep 1157399 = 1736099) B1736099
theorem B1157419 : Blo 1156638 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B1157431 : Blo 1156638 1157431 := bstep (se 1 (by rfl) ⟨868073, by rfl⟩ : syracuseStep 1157431 = 1736147) B1736147
theorem B1157451 : Blo 1156638 1157451 := bstep (se 1 (by rfl) ⟨868088, by rfl⟩ : syracuseStep 1157451 = 1736177) B1736177
theorem B1157463 : Blo 1156638 1157463 := bstep (se 1 (by rfl) ⟨868097, by rfl⟩ : syracuseStep 1157463 = 1736195) B1736195
theorem B3909977 : Blo 1156638 3909977 := bstep (se 2 (by rfl) ⟨1466241, by rfl⟩ : syracuseStep 3909977 = 2932483) B2932483
theorem B1157483 : Blo 1156638 1157483 := bstep (se 1 (by rfl) ⟨868112, by rfl⟩ : syracuseStep 1157483 = 1736225) B1736225
theorem B1157495 : Blo 1156638 1157495 := bstep (se 1 (by rfl) ⟨868121, by rfl⟩ : syracuseStep 1157495 = 1736243) B1736243
theorem B9906563 : Blo 1156638 9906563 := bstep (se 1 (by rfl) ⟨7429922, by rfl⟩ : syracuseStep 9906563 = 14859845) B14859845
theorem B1157515 : Blo 1156638 1157515 := bstep (se 1 (by rfl) ⟨868136, by rfl⟩ : syracuseStep 1157515 = 1736273) B1736273
theorem B1157527 : Blo 1156638 1157527 := bstep (se 1 (by rfl) ⟨868145, by rfl⟩ : syracuseStep 1157527 = 1736291) B1736291
theorem B1157547 : Blo 1156638 1157547 := bstep (se 1 (by rfl) ⟨868160, by rfl⟩ : syracuseStep 1157547 = 1736321) B1736321
theorem B1157559 : Blo 1156638 1157559 := bstep (se 1 (by rfl) ⟨868169, by rfl⟩ : syracuseStep 1157559 = 1736339) B1736339
theorem B1157579 : Blo 1156638 1157579 := bstep (se 1 (by rfl) ⟨868184, by rfl⟩ : syracuseStep 1157579 = 1736369) B1736369
theorem B4401611 : Blo 1156638 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B1157591 : Blo 1156638 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B1157611 : Blo 1156638 1157611 := bstep (se 1 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 1157611 = 1736417) B1736417
theorem B1157623 : Blo 1156638 1157623 := bstep (se 1 (by rfl) ⟨868217, by rfl⟩ : syracuseStep 1157623 = 1736435) B1736435
theorem B1157643 : Blo 1156638 1157643 := bstep (se 1 (by rfl) ⟨868232, by rfl⟩ : syracuseStep 1157643 = 1736465) B1736465
theorem B1157655 : Blo 1156638 1157655 := bstep (se 1 (by rfl) ⟨868241, by rfl⟩ : syracuseStep 1157655 = 1736483) B1736483
theorem B1157675 : Blo 1156638 1157675 := bstep (se 1 (by rfl) ⟨868256, by rfl⟩ : syracuseStep 1157675 = 1736513) B1736513
theorem B1157687 : Blo 1156638 1157687 := bstep (se 1 (by rfl) ⟨868265, by rfl⟩ : syracuseStep 1157687 = 1736531) B1736531
theorem B1157707 : Blo 1156638 1157707 := bstep (se 1 (by rfl) ⟨868280, by rfl⟩ : syracuseStep 1157707 = 1736561) B1736561
theorem B1157719 : Blo 1156638 1157719 := bstep (se 1 (by rfl) ⟨868289, by rfl⟩ : syracuseStep 1157719 = 1736579) B1736579
theorem B3713629 : Blo 1156638 3713629 := bstep (se 3 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 3713629 = 1392611) B1392611
theorem B1157739 : Blo 1156638 1157739 := bstep (se 1 (by rfl) ⟨868304, by rfl⟩ : syracuseStep 1157739 = 1736609) B1736609
theorem B1157751 : Blo 1156638 1157751 := bstep (se 1 (by rfl) ⟨868313, by rfl⟩ : syracuseStep 1157751 = 1736627) B1736627
theorem B1157771 : Blo 1156638 1157771 := bstep (se 1 (by rfl) ⟨868328, by rfl⟩ : syracuseStep 1157771 = 1736657) B1736657
theorem B4401809 : Blo 1156638 4401809 := bstep (se 2 (by rfl) ⟨1650678, by rfl⟩ : syracuseStep 4401809 = 3301357) B3301357
theorem B1157783 : Blo 1156638 1157783 := bstep (se 1 (by rfl) ⟨868337, by rfl⟩ : syracuseStep 1157783 = 1736675) B1736675
theorem B1157803 : Blo 1156638 1157803 := bstep (se 1 (by rfl) ⟨868352, by rfl⟩ : syracuseStep 1157803 = 1736705) B1736705
theorem B1157815 : Blo 1156638 1157815 := bstep (se 1 (by rfl) ⟨868361, by rfl⟩ : syracuseStep 1157815 = 1736723) B1736723
theorem B1157835 : Blo 1156638 1157835 := bstep (se 1 (by rfl) ⟨868376, by rfl⟩ : syracuseStep 1157835 = 1736753) B1736753
theorem B1157847 : Blo 1156638 1157847 := bstep (se 1 (by rfl) ⟨868385, by rfl⟩ : syracuseStep 1157847 = 1736771) B1736771
theorem B1157867 : Blo 1156638 1157867 := bstep (se 1 (by rfl) ⟨868400, by rfl⟩ : syracuseStep 1157867 = 1736801) B1736801
theorem B1157879 : Blo 1156638 1157879 := bstep (se 1 (by rfl) ⟨868409, by rfl⟩ : syracuseStep 1157879 = 1736819) B1736819
theorem B1157899 : Blo 1156638 1157899 := bstep (se 1 (by rfl) ⟨868424, by rfl⟩ : syracuseStep 1157899 = 1736849) B1736849
theorem B1157911 : Blo 1156638 1157911 := bstep (se 1 (by rfl) ⟨868433, by rfl⟩ : syracuseStep 1157911 = 1736867) B1736867
theorem B1649431 : Blo 1156638 1649431 := bstep (se 1 (by rfl) ⟨1237073, by rfl⟩ : syracuseStep 1649431 = 2474147) B2474147
theorem B1157931 : Blo 1156638 1157931 := bstep (se 1 (by rfl) ⟨868448, by rfl⟩ : syracuseStep 1157931 = 1736897) B1736897
theorem B1157943 : Blo 1156638 1157943 := bstep (se 1 (by rfl) ⟨868457, by rfl⟩ : syracuseStep 1157943 = 1736915) B1736915
theorem B1157963 : Blo 1156638 1157963 := bstep (se 1 (by rfl) ⟨868472, by rfl⟩ : syracuseStep 1157963 = 1736945) B1736945
theorem B1157975 : Blo 1156638 1157975 := bstep (se 1 (by rfl) ⟨868481, by rfl⟩ : syracuseStep 1157975 = 1736963) B1736963
theorem B1157995 : Blo 1156638 1157995 := bstep (se 1 (by rfl) ⟨868496, by rfl⟩ : syracuseStep 1157995 = 1736993) B1736993
theorem B1158007 : Blo 1156638 1158007 := bstep (se 1 (by rfl) ⟨868505, by rfl⟩ : syracuseStep 1158007 = 1737011) B1737011
theorem B1158027 : Blo 1156638 1158027 := bstep (se 1 (by rfl) ⟨868520, by rfl⟩ : syracuseStep 1158027 = 1737041) B1737041
theorem B1158039 : Blo 1156638 1158039 := bstep (se 1 (by rfl) ⟨868529, by rfl⟩ : syracuseStep 1158039 = 1737059) B1737059
theorem B1158059 : Blo 1156638 1158059 := bstep (se 1 (by rfl) ⟨868544, by rfl⟩ : syracuseStep 1158059 = 1737089) B1737089
theorem B1158071 : Blo 1156638 1158071 := bstep (se 1 (by rfl) ⟨868553, by rfl⟩ : syracuseStep 1158071 = 1737107) B1737107
theorem B1158091 : Blo 1156638 1158091 := bstep (se 1 (by rfl) ⟨868568, by rfl⟩ : syracuseStep 1158091 = 1737137) B1737137
theorem B1158103 : Blo 1156638 1158103 := bstep (se 1 (by rfl) ⟨868577, by rfl⟩ : syracuseStep 1158103 = 1737155) B1737155
theorem B1158123 : Blo 1156638 1158123 := bstep (se 1 (by rfl) ⟨868592, by rfl⟩ : syracuseStep 1158123 = 1737185) B1737185
theorem B1158135 : Blo 1156638 1158135 := bstep (se 1 (by rfl) ⟨868601, by rfl⟩ : syracuseStep 1158135 = 1737203) B1737203
theorem B1158155 : Blo 1156638 1158155 := bstep (se 1 (by rfl) ⟨868616, by rfl⟩ : syracuseStep 1158155 = 1737233) B1737233
theorem B1158167 : Blo 1156638 1158167 := bstep (se 1 (by rfl) ⟨868625, by rfl⟩ : syracuseStep 1158167 = 1737251) B1737251
theorem B3910679 : Blo 1156638 3910679 := bstep (se 1 (by rfl) ⟨2933009, by rfl⟩ : syracuseStep 3910679 = 5866019) B5866019
theorem B1158187 : Blo 1156638 1158187 := bstep (se 1 (by rfl) ⟨868640, by rfl⟩ : syracuseStep 1158187 = 1737281) B1737281
theorem B1158199 : Blo 1156638 1158199 := bstep (se 1 (by rfl) ⟨868649, by rfl⟩ : syracuseStep 1158199 = 1737299) B1737299
theorem B1158219 : Blo 1156638 1158219 := bstep (se 1 (by rfl) ⟨868664, by rfl⟩ : syracuseStep 1158219 = 1737329) B1737329
theorem B1158231 : Blo 1156638 1158231 := bstep (se 1 (by rfl) ⟨868673, by rfl⟩ : syracuseStep 1158231 = 1737347) B1737347
theorem B1158251 : Blo 1156638 1158251 := bstep (se 1 (by rfl) ⟨868688, by rfl⟩ : syracuseStep 1158251 = 1737377) B1737377
theorem B1158263 : Blo 1156638 1158263 := bstep (se 1 (by rfl) ⟨868697, by rfl⟩ : syracuseStep 1158263 = 1737395) B1737395
theorem B1158283 : Blo 1156638 1158283 := bstep (se 1 (by rfl) ⟨868712, by rfl⟩ : syracuseStep 1158283 = 1737425) B1737425
theorem B1158295 : Blo 1156638 1158295 := bstep (se 1 (by rfl) ⟨868721, by rfl⟩ : syracuseStep 1158295 = 1737443) B1737443
theorem B1158315 : Blo 1156638 1158315 := bstep (se 1 (by rfl) ⟨868736, by rfl⟩ : syracuseStep 1158315 = 1737473) B1737473
theorem B1158327 : Blo 1156638 1158327 := bstep (se 1 (by rfl) ⟨868745, by rfl⟩ : syracuseStep 1158327 = 1737491) B1737491
theorem B1158347 : Blo 1156638 1158347 := bstep (se 1 (by rfl) ⟨868760, by rfl⟩ : syracuseStep 1158347 = 1737521) B1737521
theorem B1158359 : Blo 1156638 1158359 := bstep (se 1 (by rfl) ⟨868769, by rfl⟩ : syracuseStep 1158359 = 1737539) B1737539
theorem B5287133 : Blo 1156638 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B1158379 : Blo 1156638 1158379 := bstep (se 1 (by rfl) ⟨868784, by rfl⟩ : syracuseStep 1158379 = 1737569) B1737569
theorem B1158391 : Blo 1156638 1158391 := bstep (se 1 (by rfl) ⟨868793, by rfl⟩ : syracuseStep 1158391 = 1737587) B1737587
theorem B1158411 : Blo 1156638 1158411 := bstep (se 1 (by rfl) ⟨868808, by rfl⟩ : syracuseStep 1158411 = 1737617) B1737617
theorem B1158423 : Blo 1156638 1158423 := bstep (se 1 (by rfl) ⟨868817, by rfl⟩ : syracuseStep 1158423 = 1737635) B1737635
theorem B1158443 : Blo 1156638 1158443 := bstep (se 1 (by rfl) ⟨868832, by rfl⟩ : syracuseStep 1158443 = 1737665) B1737665
theorem B1158455 : Blo 1156638 1158455 := bstep (se 1 (by rfl) ⟨868841, by rfl⟩ : syracuseStep 1158455 = 1737683) B1737683
theorem B2927947 : Blo 1156638 2927947 := bstep (se 1 (by rfl) ⟨2195960, by rfl⟩ : syracuseStep 2927947 = 4391921) B4391921
theorem B1158475 : Blo 1156638 1158475 := bstep (se 1 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 1158475 = 1737713) B1737713
theorem B1158487 : Blo 1156638 1158487 := bstep (se 1 (by rfl) ⟨868865, by rfl⟩ : syracuseStep 1158487 = 1737731) B1737731
theorem B1158507 : Blo 1156638 1158507 := bstep (se 1 (by rfl) ⟨868880, by rfl⟩ : syracuseStep 1158507 = 1737761) B1737761
theorem B1158519 : Blo 1156638 1158519 := bstep (se 1 (by rfl) ⟨868889, by rfl⟩ : syracuseStep 1158519 = 1737779) B1737779
theorem B1158539 : Blo 1156638 1158539 := bstep (se 1 (by rfl) ⟨868904, by rfl⟩ : syracuseStep 1158539 = 1737809) B1737809
theorem B1158551 : Blo 1156638 1158551 := bstep (se 1 (by rfl) ⟨868913, by rfl⟩ : syracuseStep 1158551 = 1737827) B1737827
theorem B4402583 : Blo 1156638 4402583 := bstep (se 1 (by rfl) ⟨3301937, by rfl⟩ : syracuseStep 4402583 = 6603875) B6603875
theorem B1158571 : Blo 1156638 1158571 := bstep (se 1 (by rfl) ⟨868928, by rfl⟩ : syracuseStep 1158571 = 1737857) B1737857
theorem B1158583 : Blo 1156638 1158583 := bstep (se 1 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 1158583 = 1737875) B1737875
theorem B1158603 : Blo 1156638 1158603 := bstep (se 1 (by rfl) ⟨868952, by rfl⟩ : syracuseStep 1158603 = 1737905) B1737905
theorem B1158615 : Blo 1156638 1158615 := bstep (se 1 (by rfl) ⟨868961, by rfl⟩ : syracuseStep 1158615 = 1737923) B1737923
theorem B2928089 : Blo 1156638 2928089 := bstep (se 2 (by rfl) ⟨1098033, by rfl⟩ : syracuseStep 2928089 = 2196067) B2196067
theorem B1650137 : Blo 1156638 1650137 := bstep (se 2 (by rfl) ⟨618801, by rfl⟩ : syracuseStep 1650137 = 1237603) B1237603
theorem B1158635 : Blo 1156638 1158635 := bstep (se 1 (by rfl) ⟨868976, by rfl⟩ : syracuseStep 1158635 = 1737953) B1737953
theorem B1158647 : Blo 1156638 1158647 := bstep (se 1 (by rfl) ⟨868985, by rfl⟩ : syracuseStep 1158647 = 1737971) B1737971
theorem B1158667 : Blo 1156638 1158667 := bstep (se 1 (by rfl) ⟨869000, by rfl⟩ : syracuseStep 1158667 = 1738001) B1738001
theorem B1158679 : Blo 1156638 1158679 := bstep (se 1 (by rfl) ⟨869009, by rfl⟩ : syracuseStep 1158679 = 1738019) B1738019
theorem B1158699 : Blo 1156638 1158699 := bstep (se 1 (by rfl) ⟨869024, by rfl⟩ : syracuseStep 1158699 = 1738049) B1738049
theorem B3911219 : Blo 1156638 3911219 := bstep (se 1 (by rfl) ⟨2933414, by rfl⟩ : syracuseStep 3911219 = 5866829) B5866829
theorem B1158711 : Blo 1156638 1158711 := bstep (se 1 (by rfl) ⟨869033, by rfl⟩ : syracuseStep 1158711 = 1738067) B1738067
theorem B1158731 : Blo 1156638 1158731 := bstep (se 1 (by rfl) ⟨869048, by rfl⟩ : syracuseStep 1158731 = 1738097) B1738097
theorem B1650251 : Blo 1156638 1650251 := bstep (se 1 (by rfl) ⟨1237688, by rfl⟩ : syracuseStep 1650251 = 2475377) B2475377
theorem B1158743 : Blo 1156638 1158743 := bstep (se 1 (by rfl) ⟨869057, by rfl⟩ : syracuseStep 1158743 = 1738115) B1738115
theorem B4402781 : Blo 1156638 4402781 := bstep (se 3 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 4402781 = 1651043) B1651043
theorem B1158763 : Blo 1156638 1158763 := bstep (se 1 (by rfl) ⟨869072, by rfl⟩ : syracuseStep 1158763 = 1738145) B1738145
theorem B1158775 : Blo 1156638 1158775 := bstep (se 1 (by rfl) ⟨869081, by rfl⟩ : syracuseStep 1158775 = 1738163) B1738163
theorem B1158795 : Blo 1156638 1158795 := bstep (se 1 (by rfl) ⟨869096, by rfl⟩ : syracuseStep 1158795 = 1738193) B1738193
theorem B1158807 : Blo 1156638 1158807 := bstep (se 1 (by rfl) ⟨869105, by rfl⟩ : syracuseStep 1158807 = 1738211) B1738211
theorem B1158827 : Blo 1156638 1158827 := bstep (se 1 (by rfl) ⟨869120, by rfl⟩ : syracuseStep 1158827 = 1738241) B1738241
theorem B1158839 : Blo 1156638 1158839 := bstep (se 1 (by rfl) ⟨869129, by rfl⟩ : syracuseStep 1158839 = 1738259) B1738259
theorem B1158859 : Blo 1156638 1158859 := bstep (se 1 (by rfl) ⟨869144, by rfl⟩ : syracuseStep 1158859 = 1738289) B1738289
theorem B1158871 : Blo 1156638 1158871 := bstep (se 1 (by rfl) ⟨869153, by rfl⟩ : syracuseStep 1158871 = 1738307) B1738307
theorem B6598361 : Blo 1156638 6598361 := bstep (se 2 (by rfl) ⟨2474385, by rfl⟩ : syracuseStep 6598361 = 4948771) B4948771
theorem B1158891 : Blo 1156638 1158891 := bstep (se 1 (by rfl) ⟨869168, by rfl⟩ : syracuseStep 1158891 = 1738337) B1738337
theorem B1158903 : Blo 1156638 1158903 := bstep (se 1 (by rfl) ⟨869177, by rfl⟩ : syracuseStep 1158903 = 1738355) B1738355
theorem B1158923 : Blo 1156638 1158923 := bstep (se 1 (by rfl) ⟨869192, by rfl⟩ : syracuseStep 1158923 = 1738385) B1738385
theorem B1158935 : Blo 1156638 1158935 := bstep (se 1 (by rfl) ⟨869201, by rfl⟩ : syracuseStep 1158935 = 1738403) B1738403
theorem B1158955 : Blo 1156638 1158955 := bstep (se 1 (by rfl) ⟨869216, by rfl⟩ : syracuseStep 1158955 = 1738433) B1738433
theorem B1158967 : Blo 1156638 1158967 := bstep (se 1 (by rfl) ⟨869225, by rfl⟩ : syracuseStep 1158967 = 1738451) B1738451
theorem B3911489 : Blo 1156638 3911489 := bstep (se 2 (by rfl) ⟨1466808, by rfl⟩ : syracuseStep 3911489 = 2933617) B2933617
theorem B1158987 : Blo 1156638 1158987 := bstep (se 1 (by rfl) ⟨869240, by rfl⟩ : syracuseStep 1158987 = 1738481) B1738481
theorem B1158999 : Blo 1156638 1158999 := bstep (se 1 (by rfl) ⟨869249, by rfl⟩ : syracuseStep 1158999 = 1738499) B1738499
theorem B1159019 : Blo 1156638 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B1159031 : Blo 1156638 1159031 := bstep (se 1 (by rfl) ⟨869273, by rfl⟩ : syracuseStep 1159031 = 1738547) B1738547
theorem B1159051 : Blo 1156638 1159051 := bstep (se 1 (by rfl) ⟨869288, by rfl⟩ : syracuseStep 1159051 = 1738577) B1738577
theorem B4173713 : Blo 1156638 4173713 := bstep (se 2 (by rfl) ⟨1565142, by rfl⟩ : syracuseStep 4173713 = 3130285) B3130285
theorem B1159063 : Blo 1156638 1159063 := bstep (se 1 (by rfl) ⟨869297, by rfl⟩ : syracuseStep 1159063 = 1738595) B1738595
theorem B1159083 : Blo 1156638 1159083 := bstep (se 1 (by rfl) ⟨869312, by rfl⟩ : syracuseStep 1159083 = 1738625) B1738625
theorem B1159095 : Blo 1156638 1159095 := bstep (se 1 (by rfl) ⟨869321, by rfl⟩ : syracuseStep 1159095 = 1738643) B1738643
theorem B1159115 : Blo 1156638 1159115 := bstep (se 1 (by rfl) ⟨869336, by rfl⟩ : syracuseStep 1159115 = 1738673) B1738673
theorem B1159127 : Blo 1156638 1159127 := bstep (se 1 (by rfl) ⟨869345, by rfl⟩ : syracuseStep 1159127 = 1738691) B1738691
theorem B1159147 : Blo 1156638 1159147 := bstep (se 1 (by rfl) ⟨869360, by rfl⟩ : syracuseStep 1159147 = 1738721) B1738721
theorem B1159159 : Blo 1156638 1159159 := bstep (se 1 (by rfl) ⟨869369, by rfl⟩ : syracuseStep 1159159 = 1738739) B1738739
theorem B1159179 : Blo 1156638 1159179 := bstep (se 1 (by rfl) ⟨869384, by rfl⟩ : syracuseStep 1159179 = 1738769) B1738769
theorem B1159191 : Blo 1156638 1159191 := bstep (se 1 (by rfl) ⟨869393, by rfl⟩ : syracuseStep 1159191 = 1738787) B1738787
theorem B1159211 : Blo 1156638 1159211 := bstep (se 1 (by rfl) ⟨869408, by rfl⟩ : syracuseStep 1159211 = 1738817) B1738817
theorem B1159223 : Blo 1156638 1159223 := bstep (se 1 (by rfl) ⟨869417, by rfl⟩ : syracuseStep 1159223 = 1738835) B1738835
theorem B1159243 : Blo 1156638 1159243 := bstep (se 1 (by rfl) ⟨869432, by rfl⟩ : syracuseStep 1159243 = 1738865) B1738865
theorem B1159255 : Blo 1156638 1159255 := bstep (se 1 (by rfl) ⟨869441, by rfl⟩ : syracuseStep 1159255 = 1738883) B1738883
theorem B1650775 : Blo 1156638 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B1159275 : Blo 1156638 1159275 := bstep (se 1 (by rfl) ⟨869456, by rfl⟩ : syracuseStep 1159275 = 1738913) B1738913
theorem B1159287 : Blo 1156638 1159287 := bstep (se 1 (by rfl) ⟨869465, by rfl⟩ : syracuseStep 1159287 = 1738931) B1738931
theorem B1159307 : Blo 1156638 1159307 := bstep (se 1 (by rfl) ⟨869480, by rfl⟩ : syracuseStep 1159307 = 1738961) B1738961
theorem B1159319 : Blo 1156638 1159319 := bstep (se 1 (by rfl) ⟨869489, by rfl⟩ : syracuseStep 1159319 = 1738979) B1738979
theorem B1159339 : Blo 1156638 1159339 := bstep (se 1 (by rfl) ⟨869504, by rfl⟩ : syracuseStep 1159339 = 1739009) B1739009
theorem B1159351 : Blo 1156638 1159351 := bstep (se 1 (by rfl) ⟨869513, by rfl⟩ : syracuseStep 1159351 = 1739027) B1739027
theorem B1159371 : Blo 1156638 1159371 := bstep (se 1 (by rfl) ⟨869528, by rfl⟩ : syracuseStep 1159371 = 1739057) B1739057
theorem B1159383 : Blo 1156638 1159383 := bstep (se 1 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 1159383 = 1739075) B1739075
theorem B1159403 : Blo 1156638 1159403 := bstep (se 1 (by rfl) ⟨869552, by rfl⟩ : syracuseStep 1159403 = 1739105) B1739105
theorem B1159415 : Blo 1156638 1159415 := bstep (se 1 (by rfl) ⟨869561, by rfl⟩ : syracuseStep 1159415 = 1739123) B1739123
theorem B1159435 : Blo 1156638 1159435 := bstep (se 1 (by rfl) ⟨869576, by rfl⟩ : syracuseStep 1159435 = 1739153) B1739153
theorem B2928919 : Blo 1156638 2928919 := bstep (se 1 (by rfl) ⟨2196689, by rfl⟩ : syracuseStep 2928919 = 4393379) B4393379
theorem B1159447 : Blo 1156638 1159447 := bstep (se 1 (by rfl) ⟨869585, by rfl⟩ : syracuseStep 1159447 = 1739171) B1739171
theorem B1159467 : Blo 1156638 1159467 := bstep (se 1 (by rfl) ⟨869600, by rfl⟩ : syracuseStep 1159467 = 1739201) B1739201
theorem B1159479 : Blo 1156638 1159479 := bstep (se 1 (by rfl) ⟨869609, by rfl⟩ : syracuseStep 1159479 = 1739219) B1739219
theorem B1159499 : Blo 1156638 1159499 := bstep (se 1 (by rfl) ⟨869624, by rfl⟩ : syracuseStep 1159499 = 1739249) B1739249
theorem B1159511 : Blo 1156638 1159511 := bstep (se 1 (by rfl) ⟨869633, by rfl⟩ : syracuseStep 1159511 = 1739267) B1739267
theorem B3912029 : Blo 1156638 3912029 := bstep (se 3 (by rfl) ⟨733505, by rfl⟩ : syracuseStep 3912029 = 1467011) B1467011
theorem B7418213 : Blo 1156638 7418213 := bstep (se 4 (by rfl) ⟨695457, by rfl⟩ : syracuseStep 7418213 = 1390915) B1390915
theorem B1159531 : Blo 1156638 1159531 := bstep (se 1 (by rfl) ⟨869648, by rfl⟩ : syracuseStep 1159531 = 1739297) B1739297
theorem B1159543 : Blo 1156638 1159543 := bstep (se 1 (by rfl) ⟨869657, by rfl⟩ : syracuseStep 1159543 = 1739315) B1739315
theorem B1159563 : Blo 1156638 1159563 := bstep (se 1 (by rfl) ⟨869672, by rfl⟩ : syracuseStep 1159563 = 1739345) B1739345
theorem B1159575 : Blo 1156638 1159575 := bstep (se 1 (by rfl) ⟨869681, by rfl⟩ : syracuseStep 1159575 = 1739363) B1739363
theorem B1159595 : Blo 1156638 1159595 := bstep (se 1 (by rfl) ⟨869696, by rfl⟩ : syracuseStep 1159595 = 1739393) B1739393
theorem B13218227 : Blo 1156638 13218227 := bstep (se 1 (by rfl) ⟨9913670, by rfl⟩ : syracuseStep 13218227 = 19827341) B19827341
theorem B1159607 : Blo 1156638 1159607 := bstep (se 1 (by rfl) ⟨869705, by rfl⟩ : syracuseStep 1159607 = 1739411) B1739411
theorem B1159627 : Blo 1156638 1159627 := bstep (se 1 (by rfl) ⟨869720, by rfl⟩ : syracuseStep 1159627 = 1739441) B1739441
theorem B1159639 : Blo 1156638 1159639 := bstep (se 1 (by rfl) ⟨869729, by rfl⟩ : syracuseStep 1159639 = 1739459) B1739459
theorem B1159659 : Blo 1156638 1159659 := bstep (se 1 (by rfl) ⟨869744, by rfl⟩ : syracuseStep 1159659 = 1739489) B1739489
theorem B1159671 : Blo 1156638 1159671 := bstep (se 1 (by rfl) ⟨869753, by rfl⟩ : syracuseStep 1159671 = 1739507) B1739507
theorem B1159691 : Blo 1156638 1159691 := bstep (se 1 (by rfl) ⟨869768, by rfl⟩ : syracuseStep 1159691 = 1739537) B1739537
theorem B75280913 : Blo 1156638 75280913 := bstep (se 2 (by rfl) ⟨28230342, by rfl⟩ : syracuseStep 75280913 = 56460685) B56460685
theorem B1159703 : Blo 1156638 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B1159723 : Blo 1156638 1159723 := bstep (se 1 (by rfl) ⟨869792, by rfl⟩ : syracuseStep 1159723 = 1739585) B1739585
theorem B1159735 : Blo 1156638 1159735 := bstep (se 1 (by rfl) ⟨869801, by rfl⟩ : syracuseStep 1159735 = 1739603) B1739603
theorem B1159755 : Blo 1156638 1159755 := bstep (se 1 (by rfl) ⟨869816, by rfl⟩ : syracuseStep 1159755 = 1739633) B1739633
theorem B1159767 : Blo 1156638 1159767 := bstep (se 1 (by rfl) ⟨869825, by rfl⟩ : syracuseStep 1159767 = 1739651) B1739651
theorem B1159787 : Blo 1156638 1159787 := bstep (se 1 (by rfl) ⟨869840, by rfl⟩ : syracuseStep 1159787 = 1739681) B1739681
theorem B1159799 : Blo 1156638 1159799 := bstep (se 1 (by rfl) ⟨869849, by rfl⟩ : syracuseStep 1159799 = 1739699) B1739699
theorem B1159819 : Blo 1156638 1159819 := bstep (se 1 (by rfl) ⟨869864, by rfl⟩ : syracuseStep 1159819 = 1739729) B1739729
theorem B1159831 : Blo 1156638 1159831 := bstep (se 1 (by rfl) ⟨869873, by rfl⟩ : syracuseStep 1159831 = 1739747) B1739747
theorem B1159851 : Blo 1156638 1159851 := bstep (se 1 (by rfl) ⟨869888, by rfl⟩ : syracuseStep 1159851 = 1739777) B1739777
theorem B1159863 : Blo 1156638 1159863 := bstep (se 1 (by rfl) ⟨869897, by rfl⟩ : syracuseStep 1159863 = 1739795) B1739795
theorem B2929355 : Blo 1156638 2929355 := bstep (se 1 (by rfl) ⟨2197016, by rfl⟩ : syracuseStep 2929355 = 4394033) B4394033
theorem B1159883 : Blo 1156638 1159883 := bstep (se 1 (by rfl) ⟨869912, by rfl⟩ : syracuseStep 1159883 = 1739825) B1739825
theorem B1159895 : Blo 1156638 1159895 := bstep (se 1 (by rfl) ⟨869921, by rfl⟩ : syracuseStep 1159895 = 1739843) B1739843
theorem B1159915 : Blo 1156638 1159915 := bstep (se 1 (by rfl) ⟨869936, by rfl⟩ : syracuseStep 1159915 = 1739873) B1739873
theorem B1159927 : Blo 1156638 1159927 := bstep (se 1 (by rfl) ⟨869945, by rfl⟩ : syracuseStep 1159927 = 1739891) B1739891
theorem B1159947 : Blo 1156638 1159947 := bstep (se 1 (by rfl) ⟨869960, by rfl⟩ : syracuseStep 1159947 = 1739921) B1739921
theorem B1159959 : Blo 1156638 1159959 := bstep (se 1 (by rfl) ⟨869969, by rfl⟩ : syracuseStep 1159959 = 1739939) B1739939
theorem B1159979 : Blo 1156638 1159979 := bstep (se 1 (by rfl) ⟨869984, by rfl⟩ : syracuseStep 1159979 = 1739969) B1739969
theorem B1159991 : Blo 1156638 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B7418699 : Blo 1156638 7418699 := bstep (se 1 (by rfl) ⟨5564024, by rfl⟩ : syracuseStep 7418699 = 11128049) B11128049
theorem B1160011 : Blo 1156638 1160011 := bstep (se 1 (by rfl) ⟨870008, by rfl⟩ : syracuseStep 1160011 = 1740017) B1740017
theorem B1160023 : Blo 1156638 1160023 := bstep (se 1 (by rfl) ⟨870017, by rfl⟩ : syracuseStep 1160023 = 1740035) B1740035
theorem B1160043 : Blo 1156638 1160043 := bstep (se 1 (by rfl) ⟨870032, by rfl⟩ : syracuseStep 1160043 = 1740065) B1740065
theorem B1160055 : Blo 1156638 1160055 := bstep (se 1 (by rfl) ⟨870041, by rfl⟩ : syracuseStep 1160055 = 1740083) B1740083
theorem B1651595 : Blo 1156638 1651595 := bstep (se 1 (by rfl) ⟨1238696, by rfl⟩ : syracuseStep 1651595 = 2477393) B2477393
theorem B1160075 : Blo 1156638 1160075 := bstep (se 1 (by rfl) ⟨870056, by rfl⟩ : syracuseStep 1160075 = 1740113) B1740113
theorem B1160087 : Blo 1156638 1160087 := bstep (se 1 (by rfl) ⟨870065, by rfl⟩ : syracuseStep 1160087 = 1740131) B1740131
theorem B1160107 : Blo 1156638 1160107 := bstep (se 1 (by rfl) ⟨870080, by rfl⟩ : syracuseStep 1160107 = 1740161) B1740161
theorem B1160119 : Blo 1156638 1160119 := bstep (se 1 (by rfl) ⟨870089, by rfl⟩ : syracuseStep 1160119 = 1740179) B1740179
theorem B1160139 : Blo 1156638 1160139 := bstep (se 1 (by rfl) ⟨870104, by rfl⟩ : syracuseStep 1160139 = 1740209) B1740209
theorem B1160151 : Blo 1156638 1160151 := bstep (se 1 (by rfl) ⟨870113, by rfl⟩ : syracuseStep 1160151 = 1740227) B1740227
theorem B1160171 : Blo 1156638 1160171 := bstep (se 1 (by rfl) ⟨870128, by rfl⟩ : syracuseStep 1160171 = 1740257) B1740257
theorem B1160183 : Blo 1156638 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B8795141 : Blo 1156638 8795141 := bstep (se 4 (by rfl) ⟨824544, by rfl⟩ : syracuseStep 8795141 = 1649089) B1649089
theorem B1160203 : Blo 1156638 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B4174865 : Blo 1156638 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B1160215 : Blo 1156638 1160215 := bstep (se 1 (by rfl) ⟨870161, by rfl⟩ : syracuseStep 1160215 = 1740323) B1740323
theorem B1160235 : Blo 1156638 1160235 := bstep (se 1 (by rfl) ⟨870176, by rfl⟩ : syracuseStep 1160235 = 1740353) B1740353
theorem B1160247 : Blo 1156638 1160247 := bstep (se 1 (by rfl) ⟨870185, by rfl⟩ : syracuseStep 1160247 = 1740371) B1740371
theorem B2929729 : Blo 1156638 2929729 := bstep (se 2 (by rfl) ⟨1098648, by rfl⟩ : syracuseStep 2929729 = 2197297) B2197297
theorem B1160267 : Blo 1156638 1160267 := bstep (se 1 (by rfl) ⟨870200, by rfl⟩ : syracuseStep 1160267 = 1740401) B1740401
theorem B1160279 : Blo 1156638 1160279 := bstep (se 1 (by rfl) ⟨870209, by rfl⟩ : syracuseStep 1160279 = 1740419) B1740419
theorem B1160299 : Blo 1156638 1160299 := bstep (se 1 (by rfl) ⟨870224, by rfl⟩ : syracuseStep 1160299 = 1740449) B1740449
theorem B1160311 : Blo 1156638 1160311 := bstep (se 1 (by rfl) ⟨870233, by rfl⟩ : syracuseStep 1160311 = 1740467) B1740467
theorem B14824579 : Blo 1156638 14824579 := bstep (se 1 (by rfl) ⟨11118434, by rfl⟩ : syracuseStep 14824579 = 22236869) B22236869
theorem B1160331 : Blo 1156638 1160331 := bstep (se 1 (by rfl) ⟨870248, by rfl⟩ : syracuseStep 1160331 = 1740497) B1740497
theorem B1160343 : Blo 1156638 1160343 := bstep (se 1 (by rfl) ⟨870257, by rfl⟩ : syracuseStep 1160343 = 1740515) B1740515
theorem B1160363 : Blo 1156638 1160363 := bstep (se 1 (by rfl) ⟨870272, by rfl⟩ : syracuseStep 1160363 = 1740545) B1740545
theorem B4764851 : Blo 1156638 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B1160375 : Blo 1156638 1160375 := bstep (se 1 (by rfl) ⟨870281, by rfl⟩ : syracuseStep 1160375 = 1740563) B1740563
theorem B2471105 : Blo 1156638 2471105 := bstep (se 2 (by rfl) ⟨926664, by rfl⟩ : syracuseStep 2471105 = 1853329) B1853329
theorem B1160395 : Blo 1156638 1160395 := bstep (se 1 (by rfl) ⟨870296, by rfl⟩ : syracuseStep 1160395 = 1740593) B1740593
theorem B1160407 : Blo 1156638 1160407 := bstep (se 1 (by rfl) ⟨870305, by rfl⟩ : syracuseStep 1160407 = 1740611) B1740611
theorem B1160427 : Blo 1156638 1160427 := bstep (se 1 (by rfl) ⟨870320, by rfl⟩ : syracuseStep 1160427 = 1740641) B1740641
theorem B1160439 : Blo 1156638 1160439 := bstep (se 1 (by rfl) ⟨870329, by rfl⟩ : syracuseStep 1160439 = 1740659) B1740659
theorem B1160459 : Blo 1156638 1160459 := bstep (se 1 (by rfl) ⟨870344, by rfl⟩ : syracuseStep 1160459 = 1740689) B1740689
theorem B1160471 : Blo 1156638 1160471 := bstep (se 1 (by rfl) ⟨870353, by rfl⟩ : syracuseStep 1160471 = 1740707) B1740707
theorem B9909539 : Blo 1156638 9909539 := bstep (se 1 (by rfl) ⟨7432154, by rfl⟩ : syracuseStep 9909539 = 14864309) B14864309
theorem B1160491 : Blo 1156638 1160491 := bstep (se 1 (by rfl) ⟨870368, by rfl⟩ : syracuseStep 1160491 = 1740737) B1740737
theorem B1160503 : Blo 1156638 1160503 := bstep (se 1 (by rfl) ⟨870377, by rfl⟩ : syracuseStep 1160503 = 1740755) B1740755
theorem B6600001 : Blo 1156638 6600001 := bstep (se 2 (by rfl) ⟨2475000, by rfl⟩ : syracuseStep 6600001 = 4950001) B4950001
theorem B1160523 : Blo 1156638 1160523 := bstep (se 1 (by rfl) ⟨870392, by rfl⟩ : syracuseStep 1160523 = 1740785) B1740785
theorem B1160535 : Blo 1156638 1160535 := bstep (se 1 (by rfl) ⟨870401, by rfl⟩ : syracuseStep 1160535 = 1740803) B1740803
theorem B1160555 : Blo 1156638 1160555 := bstep (se 1 (by rfl) ⟨870416, by rfl⟩ : syracuseStep 1160555 = 1740833) B1740833
theorem B1160567 : Blo 1156638 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B1160587 : Blo 1156638 1160587 := bstep (se 1 (by rfl) ⟨870440, by rfl⟩ : syracuseStep 1160587 = 1740881) B1740881
theorem B1160599 : Blo 1156638 1160599 := bstep (se 1 (by rfl) ⟨870449, by rfl⟩ : syracuseStep 1160599 = 1740899) B1740899
theorem B1160619 : Blo 1156638 1160619 := bstep (se 1 (by rfl) ⟨870464, by rfl⟩ : syracuseStep 1160619 = 1740929) B1740929
theorem B1160631 : Blo 1156638 1160631 := bstep (se 1 (by rfl) ⟨870473, by rfl⟩ : syracuseStep 1160631 = 1740947) B1740947
theorem B3913163 : Blo 1156638 3913163 := bstep (se 1 (by rfl) ⟨2934872, by rfl⟩ : syracuseStep 3913163 = 5869745) B5869745
theorem B2602457 : Blo 1156638 2602457 := bstep (se 2 (by rfl) ⟨975921, by rfl⟩ : syracuseStep 2602457 = 1951843) B1951843
theorem B4404739 : Blo 1156638 4404739 := bstep (se 1 (by rfl) ⟨3303554, by rfl⟩ : syracuseStep 4404739 = 6607109) B6607109
theorem B2471447 : Blo 1156638 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B2602547 : Blo 1156638 2602547 := bstep (se 1 (by rfl) ⟨1951910, by rfl⟩ : syracuseStep 2602547 = 3903821) B3903821
theorem B2504267 : Blo 1156638 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B2602583 : Blo 1156638 2602583 := bstep (se 1 (by rfl) ⟨1951937, by rfl⟩ : syracuseStep 2602583 = 3903875) B3903875
theorem B2930327 : Blo 1156638 2930327 := bstep (se 1 (by rfl) ⟨2197745, by rfl⟩ : syracuseStep 2930327 = 4395491) B4395491
theorem B1980119 : Blo 1156638 1980119 := bstep (se 1 (by rfl) ⟨1485089, by rfl⟩ : syracuseStep 1980119 = 2970179) B2970179
theorem B3913433 : Blo 1156638 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B2602763 : Blo 1156638 2602763 := bstep (se 1 (by rfl) ⟨1952072, by rfl⟩ : syracuseStep 2602763 = 3904145) B3904145
theorem B4405043 : Blo 1156638 4405043 := bstep (se 1 (by rfl) ⟨3303782, by rfl⟩ : syracuseStep 4405043 = 6607565) B6607565
theorem B2602817 : Blo 1156638 2602817 := bstep (se 2 (by rfl) ⟨976056, by rfl⟩ : syracuseStep 2602817 = 1952113) B1952113
theorem B2471755 : Blo 1156638 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B13219685 : Blo 1156638 13219685 := bstep (se 4 (by rfl) ⟨1239345, by rfl⟩ : syracuseStep 13219685 = 2478691) B2478691
theorem B2603033 : Blo 1156638 2603033 := bstep (se 2 (by rfl) ⟨976137, by rfl⟩ : syracuseStep 2603033 = 1952275) B1952275
theorem B2603123 : Blo 1156638 2603123 := bstep (se 1 (by rfl) ⟨1952342, by rfl⟩ : syracuseStep 2603123 = 3904685) B3904685
theorem B2603159 : Blo 1156638 2603159 := bstep (se 1 (by rfl) ⟨1952369, by rfl⟩ : syracuseStep 2603159 = 3904739) B3904739
theorem B3127517 : Blo 1156638 3127517 := bstep (se 3 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 3127517 = 1172819) B1172819
theorem B5945645 : Blo 1156638 5945645 := bstep (se 3 (by rfl) ⟨1114808, by rfl⟩ : syracuseStep 5945645 = 2229617) B2229617
theorem B2603339 : Blo 1156638 2603339 := bstep (se 1 (by rfl) ⟨1952504, by rfl⟩ : syracuseStep 2603339 = 3905009) B3905009
theorem B2603393 : Blo 1156638 2603393 := bstep (se 2 (by rfl) ⟨976272, by rfl⟩ : syracuseStep 2603393 = 1952545) B1952545
theorem B3914135 : Blo 1156638 3914135 := bstep (se 1 (by rfl) ⟨2935601, by rfl⟩ : syracuseStep 3914135 = 5871203) B5871203
theorem B2931137 : Blo 1156638 2931137 := bstep (se 2 (by rfl) ⟨1099176, by rfl⟩ : syracuseStep 2931137 = 2198353) B2198353
theorem B4405697 : Blo 1156638 4405697 := bstep (se 2 (by rfl) ⟨1652136, by rfl⟩ : syracuseStep 4405697 = 3304273) B3304273
theorem B4176449 : Blo 1156638 4176449 := bstep (se 2 (by rfl) ⟨1566168, by rfl⟩ : syracuseStep 4176449 = 3132337) B3132337
theorem B2603609 : Blo 1156638 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B2472601 : Blo 1156638 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B2603699 : Blo 1156638 2603699 := bstep (se 1 (by rfl) ⟨1952774, by rfl⟩ : syracuseStep 2603699 = 3905549) B3905549
theorem B2603735 : Blo 1156638 2603735 := bstep (se 1 (by rfl) ⟨1952801, by rfl⟩ : syracuseStep 2603735 = 3905603) B3905603
theorem B2603915 : Blo 1156638 2603915 := bstep (se 1 (by rfl) ⟨1952936, by rfl⟩ : syracuseStep 2603915 = 3905873) B3905873
theorem B3914675 : Blo 1156638 3914675 := bstep (se 1 (by rfl) ⟨2936006, by rfl⟩ : syracuseStep 3914675 = 5872013) B5872013
theorem B2603969 : Blo 1156638 2603969 := bstep (se 2 (by rfl) ⟨976488, by rfl⟩ : syracuseStep 2603969 = 1952977) B1952977
theorem B2931673 : Blo 1156638 2931673 := bstep (se 2 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 2931673 = 2198755) B2198755
theorem B2604185 : Blo 1156638 2604185 := bstep (se 2 (by rfl) ⟨976569, by rfl⟩ : syracuseStep 2604185 = 1953139) B1953139
theorem B3914945 : Blo 1156638 3914945 := bstep (se 2 (by rfl) ⟨1468104, by rfl⟩ : syracuseStep 3914945 = 2936209) B2936209
theorem B2604275 : Blo 1156638 2604275 := bstep (se 1 (by rfl) ⟨1953206, by rfl⟩ : syracuseStep 2604275 = 3906413) B3906413
theorem B2604311 : Blo 1156638 2604311 := bstep (se 1 (by rfl) ⟨1953233, by rfl⟩ : syracuseStep 2604311 = 3906467) B3906467
theorem B8797571 : Blo 1156638 8797571 := bstep (se 1 (by rfl) ⟨6598178, by rfl⟩ : syracuseStep 8797571 = 13196357) B13196357
theorem B171589013 : Blo 1156638 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B2604491 : Blo 1156638 2604491 := bstep (se 1 (by rfl) ⟨1953368, by rfl⟩ : syracuseStep 2604491 = 3906737) B3906737
theorem B2604545 : Blo 1156638 2604545 := bstep (se 2 (by rfl) ⟨976704, by rfl⟩ : syracuseStep 2604545 = 1953409) B1953409
theorem B2604761 : Blo 1156638 2604761 := bstep (se 2 (by rfl) ⟨976785, by rfl⟩ : syracuseStep 2604761 = 1953571) B1953571
theorem B3915485 : Blo 1156638 3915485 := bstep (se 3 (by rfl) ⟨734153, by rfl⟩ : syracuseStep 3915485 = 1468307) B1468307
theorem B2604851 : Blo 1156638 2604851 := bstep (se 1 (by rfl) ⟨1953638, by rfl⟩ : syracuseStep 2604851 = 3907277) B3907277
theorem B2604887 : Blo 1156638 2604887 := bstep (se 1 (by rfl) ⟨1953665, by rfl⟩ : syracuseStep 2604887 = 3907331) B3907331
theorem B2473907 : Blo 1156638 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B2605067 : Blo 1156638 2605067 := bstep (se 1 (by rfl) ⟨1953800, by rfl⟩ : syracuseStep 2605067 = 3907601) B3907601
theorem B2932787 : Blo 1156638 2932787 := bstep (se 1 (by rfl) ⟨2199590, by rfl⟩ : syracuseStep 2932787 = 4399181) B4399181
theorem B2605121 : Blo 1156638 2605121 := bstep (se 2 (by rfl) ⟨976920, by rfl⟩ : syracuseStep 2605121 = 1953841) B1953841
theorem B4178051 : Blo 1156638 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B7422131 : Blo 1156638 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B5357789 : Blo 1156638 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B2605337 : Blo 1156638 2605337 := bstep (se 2 (by rfl) ⟨977001, by rfl⟩ : syracuseStep 2605337 = 1954003) B1954003
theorem B2933081 : Blo 1156638 2933081 := bstep (se 2 (by rfl) ⟨1099905, by rfl⟩ : syracuseStep 2933081 = 2199811) B2199811
theorem B2605427 : Blo 1156638 2605427 := bstep (se 1 (by rfl) ⟨1954070, by rfl⟩ : syracuseStep 2605427 = 3908141) B3908141
theorem B2605463 : Blo 1156638 2605463 := bstep (se 1 (by rfl) ⟨1954097, by rfl⟩ : syracuseStep 2605463 = 3908195) B3908195
theorem B2605643 : Blo 1156638 2605643 := bstep (se 1 (by rfl) ⟨1954232, by rfl⟩ : syracuseStep 2605643 = 3908465) B3908465
theorem B12534365 : Blo 1156638 12534365 := bstep (se 3 (by rfl) ⟨2350193, by rfl⟩ : syracuseStep 12534365 = 4700387) B4700387
theorem B2605697 : Blo 1156638 2605697 := bstep (se 2 (by rfl) ⟨977136, by rfl⟩ : syracuseStep 2605697 = 1954273) B1954273
theorem B6603443 : Blo 1156638 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B40682225 : Blo 1156638 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B3916619 : Blo 1156638 3916619 := bstep (se 1 (by rfl) ⟨2937464, by rfl⟩ : syracuseStep 3916619 = 5874929) B5874929
theorem B2605913 : Blo 1156638 2605913 := bstep (se 2 (by rfl) ⟨977217, by rfl⟩ : syracuseStep 2605913 = 1954435) B1954435
theorem B2606003 : Blo 1156638 2606003 := bstep (se 1 (by rfl) ⟨1954502, by rfl⟩ : syracuseStep 2606003 = 3909005) B3909005
theorem B2606039 : Blo 1156638 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B3294283 : Blo 1156638 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B3916889 : Blo 1156638 3916889 := bstep (se 2 (by rfl) ⟨1468833, by rfl⟩ : syracuseStep 3916889 = 2937667) B2937667
theorem B2606219 : Blo 1156638 2606219 := bstep (se 1 (by rfl) ⟨1954664, by rfl⟩ : syracuseStep 2606219 = 3909329) B3909329
theorem B2606273 : Blo 1156638 2606273 := bstep (se 2 (by rfl) ⟨977352, by rfl⟩ : syracuseStep 2606273 = 1954705) B1954705
theorem B4179217 : Blo 1156638 4179217 := bstep (se 2 (by rfl) ⟨1567206, by rfl⟩ : syracuseStep 4179217 = 3134413) B3134413
theorem B9389357 : Blo 1156638 9389357 := bstep (se 3 (by rfl) ⟨1760504, by rfl⟩ : syracuseStep 9389357 = 3521009) B3521009
theorem B2114905 : Blo 1156638 2114905 := bstep (se 2 (by rfl) ⟨793089, by rfl⟩ : syracuseStep 2114905 = 1586179) B1586179
theorem B3294557 : Blo 1156638 3294557 := bstep (se 3 (by rfl) ⟨617729, by rfl⟩ : syracuseStep 3294557 = 1235459) B1235459
theorem B1852811 : Blo 1156638 1852811 := bstep (se 1 (by rfl) ⟨1389608, by rfl⟩ : syracuseStep 1852811 = 2779217) B2779217
theorem B2606489 : Blo 1156638 2606489 := bstep (se 2 (by rfl) ⟨977433, by rfl⟩ : syracuseStep 2606489 = 1954867) B1954867
theorem B2475479 : Blo 1156638 2475479 := bstep (se 1 (by rfl) ⟨1856609, by rfl⟩ : syracuseStep 2475479 = 3713219) B3713219
theorem B18073049 : Blo 1156638 18073049 := bstep (se 2 (by rfl) ⟨6777393, by rfl⟩ : syracuseStep 18073049 = 13554787) B13554787
theorem B2606579 : Blo 1156638 2606579 := bstep (se 1 (by rfl) ⟨1954934, by rfl⟩ : syracuseStep 2606579 = 3909869) B3909869
theorem B2606615 : Blo 1156638 2606615 := bstep (se 1 (by rfl) ⟨1954961, by rfl⟩ : syracuseStep 2606615 = 3909923) B3909923
theorem B3720779 : Blo 1156638 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B2606795 : Blo 1156638 2606795 := bstep (se 1 (by rfl) ⟨1955096, by rfl⟩ : syracuseStep 2606795 = 3910193) B3910193
theorem B10045133 : Blo 1156638 10045133 := bstep (se 3 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 10045133 = 3766925) B3766925
theorem B2606849 : Blo 1156638 2606849 := bstep (se 2 (by rfl) ⟨977568, by rfl⟩ : syracuseStep 2606849 = 1955137) B1955137
theorem B2475787 : Blo 1156638 2475787 := bstep (se 1 (by rfl) ⟨1856840, by rfl⟩ : syracuseStep 2475787 = 3713681) B3713681
theorem B2934731 : Blo 1156638 2934731 := bstep (se 1 (by rfl) ⟨2201048, by rfl⟩ : syracuseStep 2934731 = 4402097) B4402097
theorem B2607065 : Blo 1156638 2607065 := bstep (se 2 (by rfl) ⟨977649, by rfl⟩ : syracuseStep 2607065 = 1955299) B1955299
theorem B2607155 : Blo 1156638 2607155 := bstep (se 1 (by rfl) ⟨1955366, by rfl⟩ : syracuseStep 2607155 = 3910733) B3910733
theorem B2607191 : Blo 1156638 2607191 := bstep (se 1 (by rfl) ⟨1955393, by rfl⟩ : syracuseStep 2607191 = 3910787) B3910787
theorem B6604901 : Blo 1156638 6604901 := bstep (se 4 (by rfl) ⟨619209, by rfl⟩ : syracuseStep 6604901 = 1238419) B1238419
theorem B1951897 : Blo 1156638 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B2607371 : Blo 1156638 2607371 := bstep (se 1 (by rfl) ⟨1955528, by rfl⟩ : syracuseStep 2607371 = 3911057) B3911057
theorem B2607425 : Blo 1156638 2607425 := bstep (se 2 (by rfl) ⟨977784, by rfl⟩ : syracuseStep 2607425 = 1955569) B1955569
theorem B10701233 : Blo 1156638 10701233 := bstep (se 2 (by rfl) ⟨4012962, by rfl⟩ : syracuseStep 10701233 = 8025925) B8025925
theorem B4704733 : Blo 1156638 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B2607641 : Blo 1156638 2607641 := bstep (se 2 (by rfl) ⟨977865, by rfl⟩ : syracuseStep 2607641 = 1955731) B1955731
theorem B2607731 : Blo 1156638 2607731 := bstep (se 1 (by rfl) ⟨1955798, by rfl⟩ : syracuseStep 2607731 = 3911597) B3911597
theorem B2607767 : Blo 1156638 2607767 := bstep (se 1 (by rfl) ⟨1955825, by rfl⟩ : syracuseStep 2607767 = 3911651) B3911651
theorem B8800973 : Blo 1156638 8800973 := bstep (se 3 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 8800973 = 3300365) B3300365
theorem B1952471 : Blo 1156638 1952471 := bstep (se 1 (by rfl) ⟨1464353, by rfl⟩ : syracuseStep 1952471 = 2928707) B2928707
theorem B2607947 : Blo 1156638 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B1952599 : Blo 1156638 1952599 := bstep (se 1 (by rfl) ⟨1464449, by rfl⟩ : syracuseStep 1952599 = 2928899) B2928899
theorem B2608001 : Blo 1156638 2608001 := bstep (se 2 (by rfl) ⟨978000, by rfl⟩ : syracuseStep 2608001 = 1956001) B1956001
theorem B2935703 : Blo 1156638 2935703 := bstep (se 1 (by rfl) ⟨2201777, by rfl⟩ : syracuseStep 2935703 = 4403555) B4403555
theorem B2477017 : Blo 1156638 2477017 := bstep (se 2 (by rfl) ⟨928881, by rfl⟩ : syracuseStep 2477017 = 1857763) B1857763
theorem B2608217 : Blo 1156638 2608217 := bstep (se 2 (by rfl) ⟨978081, by rfl⟩ : syracuseStep 2608217 = 1956163) B1956163
theorem B8801459 : Blo 1156638 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B2608307 : Blo 1156638 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B2608343 : Blo 1156638 2608343 := bstep (se 1 (by rfl) ⟨1956257, by rfl⟩ : syracuseStep 2608343 = 3912515) B3912515
theorem B4345177 : Blo 1156638 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B2608523 : Blo 1156638 2608523 := bstep (se 1 (by rfl) ⟨1956392, by rfl⟩ : syracuseStep 2608523 = 3912785) B3912785
theorem B2608577 : Blo 1156638 2608577 := bstep (se 2 (by rfl) ⟨978216, by rfl⟩ : syracuseStep 2608577 = 1956433) B1956433
theorem B1953227 : Blo 1156638 1953227 := bstep (se 1 (by rfl) ⟨1464920, by rfl⟩ : syracuseStep 1953227 = 2929841) B2929841
theorem B2117081 : Blo 1156638 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B2936371 : Blo 1156638 2936371 := bstep (se 1 (by rfl) ⟨2202278, by rfl⟩ : syracuseStep 2936371 = 4404557) B4404557
theorem B1953355 : Blo 1156638 1953355 := bstep (se 1 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 1953355 = 2930033) B2930033
theorem B3296857 : Blo 1156638 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B2608793 : Blo 1156638 2608793 := bstep (se 2 (by rfl) ⟨978297, by rfl⟩ : syracuseStep 2608793 = 1956595) B1956595
theorem B2936513 : Blo 1156638 2936513 := bstep (se 2 (by rfl) ⟨1101192, by rfl⟩ : syracuseStep 2936513 = 2202385) B2202385
theorem B1953497 : Blo 1156638 1953497 := bstep (se 2 (by rfl) ⟨732561, by rfl⟩ : syracuseStep 1953497 = 1465123) B1465123
theorem B2608883 : Blo 1156638 2608883 := bstep (se 1 (by rfl) ⟨1956662, by rfl⟩ : syracuseStep 2608883 = 3913325) B3913325
theorem B2608919 : Blo 1156638 2608919 := bstep (se 1 (by rfl) ⟨1956689, by rfl⟩ : syracuseStep 2608919 = 3913379) B3913379
theorem B1953625 : Blo 1156638 1953625 := bstep (se 2 (by rfl) ⟨732609, by rfl⟩ : syracuseStep 1953625 = 1465219) B1465219
theorem B2609099 : Blo 1156638 2609099 := bstep (se 1 (by rfl) ⟨1956824, by rfl⟩ : syracuseStep 2609099 = 3913649) B3913649
theorem B2609153 : Blo 1156638 2609153 := bstep (se 2 (by rfl) ⟨978432, by rfl⟩ : syracuseStep 2609153 = 1956865) B1956865
theorem B23777315 : Blo 1156638 23777315 := bstep (se 1 (by rfl) ⟨17832986, by rfl⟩ : syracuseStep 23777315 = 35665973) B35665973
theorem B3297473 : Blo 1156638 3297473 := bstep (se 2 (by rfl) ⟨1236552, by rfl⟩ : syracuseStep 3297473 = 2473105) B2473105
theorem B5558489 : Blo 1156638 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B2609369 : Blo 1156638 2609369 := bstep (se 2 (by rfl) ⟨978513, by rfl⟩ : syracuseStep 2609369 = 1957027) B1957027
theorem B114479405 : Blo 1156638 114479405 := bstep (se 3 (by rfl) ⟨21464888, by rfl⟩ : syracuseStep 114479405 = 42929777) B42929777
theorem B2609459 : Blo 1156638 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B2609495 : Blo 1156638 2609495 := bstep (se 1 (by rfl) ⟨1957121, by rfl⟩ : syracuseStep 2609495 = 3914243) B3914243
theorem B8343901 : Blo 1156638 8343901 := bstep (se 3 (by rfl) ⟨1564481, by rfl⟩ : syracuseStep 8343901 = 3128963) B3128963
theorem B9163109 : Blo 1156638 9163109 := bstep (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) B1718083
theorem B1954199 : Blo 1156638 1954199 := bstep (se 1 (by rfl) ⟨1465649, by rfl⟩ : syracuseStep 1954199 = 2931299) B2931299
theorem B2609675 : Blo 1156638 2609675 := bstep (se 1 (by rfl) ⟨1957256, by rfl⟩ : syracuseStep 2609675 = 3914513) B3914513
theorem B1954327 : Blo 1156638 1954327 := bstep (se 1 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 1954327 = 2931491) B2931491
theorem B2609729 : Blo 1156638 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B8802917 : Blo 1156638 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B2609945 : Blo 1156638 2609945 := bstep (se 2 (by rfl) ⟨978729, by rfl⟩ : syracuseStep 2609945 = 1957459) B1957459
theorem B15848257 : Blo 1156638 15848257 := bstep (se 2 (by rfl) ⟨5943096, by rfl⟩ : syracuseStep 15848257 = 11886193) B11886193
theorem B2610035 : Blo 1156638 2610035 := bstep (se 1 (by rfl) ⟨1957526, by rfl⟩ : syracuseStep 2610035 = 3915053) B3915053
theorem B2610071 : Blo 1156638 2610071 := bstep (se 1 (by rfl) ⟨1957553, by rfl⟩ : syracuseStep 2610071 = 3915107) B3915107
theorem B2937779 : Blo 1156638 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B8803403 : Blo 1156638 8803403 := bstep (se 1 (by rfl) ⟨6602552, by rfl⟩ : syracuseStep 8803403 = 13205105) B13205105
theorem B2610251 : Blo 1156638 2610251 := bstep (se 1 (by rfl) ⟨1957688, by rfl⟩ : syracuseStep 2610251 = 3915377) B3915377
theorem B2610305 : Blo 1156638 2610305 := bstep (se 2 (by rfl) ⟨978864, by rfl⟩ : syracuseStep 2610305 = 1957729) B1957729
theorem B1954955 : Blo 1156638 1954955 := bstep (se 1 (by rfl) ⟨1466216, by rfl⟩ : syracuseStep 1954955 = 2932433) B2932433
theorem B1955083 : Blo 1156638 1955083 := bstep (se 1 (by rfl) ⟨1466312, by rfl⟩ : syracuseStep 1955083 = 2932625) B2932625
theorem B2610521 : Blo 1156638 2610521 := bstep (se 2 (by rfl) ⟨978945, by rfl⟩ : syracuseStep 2610521 = 1957891) B1957891
theorem B1955225 : Blo 1156638 1955225 := bstep (se 2 (by rfl) ⟨733209, by rfl⟩ : syracuseStep 1955225 = 1466419) B1466419
theorem B2610611 : Blo 1156638 2610611 := bstep (se 1 (by rfl) ⟨1957958, by rfl⟩ : syracuseStep 2610611 = 3915917) B3915917
theorem B2119115 : Blo 1156638 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B2610647 : Blo 1156638 2610647 := bstep (se 1 (by rfl) ⟨1957985, by rfl⟩ : syracuseStep 2610647 = 3915971) B3915971
theorem B1955353 : Blo 1156638 1955353 := bstep (se 2 (by rfl) ⟨733257, by rfl⟩ : syracuseStep 1955353 = 1466515) B1466515
theorem B9655853 : Blo 1156638 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B2610827 : Blo 1156638 2610827 := bstep (se 1 (by rfl) ⟨1958120, by rfl⟩ : syracuseStep 2610827 = 3916241) B3916241
theorem B2610881 : Blo 1156638 2610881 := bstep (se 2 (by rfl) ⟨979080, by rfl⟩ : syracuseStep 2610881 = 1958161) B1958161
theorem B2086603 : Blo 1156638 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B1464151 : Blo 1156638 1464151 := bstep (se 1 (by rfl) ⟨1098113, by rfl⟩ : syracuseStep 1464151 = 2196227) B2196227
theorem B2611097 : Blo 1156638 2611097 := bstep (se 2 (by rfl) ⟨979161, by rfl⟩ : syracuseStep 2611097 = 1958323) B1958323
theorem B2611187 : Blo 1156638 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B2611223 : Blo 1156638 2611223 := bstep (se 1 (by rfl) ⟨1958417, by rfl⟩ : syracuseStep 2611223 = 3916835) B3916835
theorem B1955927 : Blo 1156638 1955927 := bstep (se 1 (by rfl) ⟨1466945, by rfl⟩ : syracuseStep 1955927 = 2933891) B2933891
theorem B11884637 : Blo 1156638 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B2611403 : Blo 1156638 2611403 := bstep (se 1 (by rfl) ⟨1958552, by rfl⟩ : syracuseStep 2611403 = 3917105) B3917105
theorem B1956055 : Blo 1156638 1956055 := bstep (se 1 (by rfl) ⟨1467041, by rfl⟩ : syracuseStep 1956055 = 2934083) B2934083
theorem B3299545 : Blo 1156638 3299545 := bstep (se 2 (by rfl) ⟨1237329, by rfl⟩ : syracuseStep 3299545 = 2474659) B2474659
theorem B7919947 : Blo 1156638 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B2415193 : Blo 1156638 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B3299933 : Blo 1156638 3299933 := bstep (se 3 (by rfl) ⟨618737, by rfl⟩ : syracuseStep 3299933 = 1237475) B1237475
theorem B1301323 : Blo 1156638 1301323 := bstep (se 1 (by rfl) ⟨975992, by rfl⟩ : syracuseStep 1301323 = 1951985) B1951985
theorem B1956683 : Blo 1156638 1956683 := bstep (se 1 (by rfl) ⟨1467512, by rfl⟩ : syracuseStep 1956683 = 2935025) B2935025
theorem B3431347 : Blo 1156638 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B1301431 : Blo 1156638 1301431 := bstep (se 1 (by rfl) ⟨976073, by rfl⟩ : syracuseStep 1301431 = 1952147) B1952147
theorem B1956811 : Blo 1156638 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B1858583 : Blo 1156638 1858583 := bstep (se 1 (by rfl) ⟨1393937, by rfl⟩ : syracuseStep 1858583 = 2787875) B2787875
theorem B2088023 : Blo 1156638 2088023 := bstep (se 1 (by rfl) ⟨1566017, by rfl⟩ : syracuseStep 2088023 = 3132035) B3132035
theorem B1956953 : Blo 1156638 1956953 := bstep (se 2 (by rfl) ⟨733857, by rfl⟩ : syracuseStep 1956953 = 1467715) B1467715
theorem B1301611 : Blo 1156638 1301611 := bstep (se 1 (by rfl) ⟨976208, by rfl⟩ : syracuseStep 1301611 = 1952417) B1952417
theorem B1858711 : Blo 1156638 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B1236151 : Blo 1156638 1236151 := bstep (se 1 (by rfl) ⟨927113, by rfl⟩ : syracuseStep 1236151 = 1854227) B1854227
theorem B2088139 : Blo 1156638 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B1858763 : Blo 1156638 1858763 := bstep (se 1 (by rfl) ⟨1394072, by rfl⟩ : syracuseStep 1858763 = 2788145) B2788145
theorem B1301719 : Blo 1156638 1301719 := bstep (se 1 (by rfl) ⟨976289, by rfl⟩ : syracuseStep 1301719 = 1952579) B1952579
theorem B1957081 : Blo 1156638 1957081 := bstep (se 2 (by rfl) ⟨733905, by rfl⟩ : syracuseStep 1957081 = 1467811) B1467811
theorem B1858891 : Blo 1156638 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B1301899 : Blo 1156638 1301899 := bstep (se 1 (by rfl) ⟨976424, by rfl⟩ : syracuseStep 1301899 = 1952849) B1952849
theorem B1302007 : Blo 1156638 1302007 := bstep (se 1 (by rfl) ⟨976505, by rfl⟩ : syracuseStep 1302007 = 1953011) B1953011
theorem B1465867 : Blo 1156638 1465867 := bstep (se 1 (by rfl) ⟨1099400, by rfl⟩ : syracuseStep 1465867 = 2198801) B2198801
theorem B5856785 : Blo 1156638 5856785 := bstep (se 2 (by rfl) ⟨2196294, by rfl⟩ : syracuseStep 5856785 = 4392589) B4392589
theorem B1302187 : Blo 1156638 1302187 := bstep (se 1 (by rfl) ⟨976640, by rfl⟩ : syracuseStep 1302187 = 1953281) B1953281
theorem B5856947 : Blo 1156638 5856947 := bstep (se 1 (by rfl) ⟨4392710, by rfl⟩ : syracuseStep 5856947 = 8785421) B8785421
theorem B1564363 : Blo 1156638 1564363 := bstep (se 1 (by rfl) ⟨1173272, by rfl⟩ : syracuseStep 1564363 = 2346545) B2346545
theorem B1302295 : Blo 1156638 1302295 := bstep (se 1 (by rfl) ⟨976721, by rfl⟩ : syracuseStep 1302295 = 1953443) B1953443
theorem B1957655 : Blo 1156638 1957655 := bstep (se 1 (by rfl) ⟨1468241, by rfl⟩ : syracuseStep 1957655 = 2936483) B2936483
theorem B1957783 : Blo 1156638 1957783 := bstep (se 1 (by rfl) ⟨1468337, by rfl⟩ : syracuseStep 1957783 = 2936675) B2936675
theorem B19783601 : Blo 1156638 19783601 := bstep (se 2 (by rfl) ⟨7418850, by rfl⟩ : syracuseStep 19783601 = 14837701) B14837701
theorem B1302475 : Blo 1156638 1302475 := bstep (se 1 (by rfl) ⟨976856, by rfl⟩ : syracuseStep 1302475 = 1953713) B1953713
theorem B1236971 : Blo 1156638 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B1302583 : Blo 1156638 1302583 := bstep (se 1 (by rfl) ⟨976937, by rfl⟩ : syracuseStep 1302583 = 1953875) B1953875
theorem B1302763 : Blo 1156638 1302763 := bstep (se 1 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 1302763 = 1954145) B1954145
theorem B1302871 : Blo 1156638 1302871 := bstep (se 1 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 1302871 = 1954307) B1954307
theorem B1761625 : Blo 1156638 1761625 := bstep (se 2 (by rfl) ⟨660609, by rfl⟩ : syracuseStep 1761625 = 1321219) B1321219
theorem B10576307 : Blo 1156638 10576307 := bstep (se 1 (by rfl) ⟨7932230, by rfl⟩ : syracuseStep 10576307 = 15864461) B15864461
theorem B1466839 : Blo 1156638 1466839 := bstep (se 1 (by rfl) ⟨1100129, by rfl⟩ : syracuseStep 1466839 = 2200259) B2200259
theorem B1303051 : Blo 1156638 1303051 := bstep (se 1 (by rfl) ⟨977288, by rfl⟩ : syracuseStep 1303051 = 1954577) B1954577
theorem B1958411 : Blo 1156638 1958411 := bstep (se 1 (by rfl) ⟨1468808, by rfl⟩ : syracuseStep 1958411 = 2937617) B2937617
theorem B1303159 : Blo 1156638 1303159 := bstep (se 1 (by rfl) ⟨977369, by rfl⟩ : syracuseStep 1303159 = 1954739) B1954739
theorem B1958539 : Blo 1156638 1958539 := bstep (se 1 (by rfl) ⟨1468904, by rfl⟩ : syracuseStep 1958539 = 2937809) B2937809
theorem B2089739 : Blo 1156638 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B1303339 : Blo 1156638 1303339 := bstep (se 1 (by rfl) ⟨977504, by rfl⟩ : syracuseStep 1303339 = 1955009) B1955009
theorem B1303447 : Blo 1156638 1303447 := bstep (se 1 (by rfl) ⟨977585, by rfl⟩ : syracuseStep 1303447 = 1955171) B1955171
theorem B1303627 : Blo 1156638 1303627 := bstep (se 1 (by rfl) ⟨977720, by rfl⟩ : syracuseStep 1303627 = 1955441) B1955441
theorem B5563523 : Blo 1156638 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B1238167 : Blo 1156638 1238167 := bstep (se 1 (by rfl) ⟨928625, by rfl⟩ : syracuseStep 1238167 = 1857251) B1857251
theorem B1303735 : Blo 1156638 1303735 := bstep (se 1 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 1303735 = 1955603) B1955603
theorem B1467659 : Blo 1156638 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B4941101 : Blo 1156638 4941101 := bstep (se 3 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 4941101 = 1852913) B1852913
theorem B1303915 : Blo 1156638 1303915 := bstep (se 1 (by rfl) ⟨977936, by rfl⟩ : syracuseStep 1303915 = 1955873) B1955873
theorem B1238423 : Blo 1156638 1238423 := bstep (se 1 (by rfl) ⟨928817, by rfl⟩ : syracuseStep 1238423 = 1857635) B1857635
theorem B3302849 : Blo 1156638 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B1304023 : Blo 1156638 1304023 := bstep (se 1 (by rfl) ⟨978017, by rfl⟩ : syracuseStep 1304023 = 1956035) B1956035
theorem B3302963 : Blo 1156638 3302963 := bstep (se 1 (by rfl) ⟨2477222, by rfl⟩ : syracuseStep 3302963 = 4954445) B4954445
theorem B5858891 : Blo 1156638 5858891 := bstep (se 1 (by rfl) ⟨4394168, by rfl⟩ : syracuseStep 5858891 = 8788337) B8788337
theorem B6350411 : Blo 1156638 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B1304203 : Blo 1156638 1304203 := bstep (se 1 (by rfl) ⟨978152, by rfl⟩ : syracuseStep 1304203 = 1956305) B1956305
theorem B2090647 : Blo 1156638 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B1304311 : Blo 1156638 1304311 := bstep (se 1 (by rfl) ⟨978233, by rfl⟩ : syracuseStep 1304311 = 1956467) B1956467
theorem B1304491 : Blo 1156638 1304491 := bstep (se 1 (by rfl) ⟨978368, by rfl⟩ : syracuseStep 1304491 = 1956737) B1956737
theorem B12707761 : Blo 1156638 12707761 := bstep (se 2 (by rfl) ⟨4765410, by rfl⟩ : syracuseStep 12707761 = 9530821) B9530821
theorem B1468363 : Blo 1156638 1468363 := bstep (se 1 (by rfl) ⟨1101272, by rfl⟩ : syracuseStep 1468363 = 2202545) B2202545
theorem B1238987 : Blo 1156638 1238987 := bstep (se 1 (by rfl) ⟨929240, by rfl⟩ : syracuseStep 1238987 = 1858481) B1858481
theorem B1304599 : Blo 1156638 1304599 := bstep (se 1 (by rfl) ⟨978449, by rfl⟩ : syracuseStep 1304599 = 1956899) B1956899
theorem B14084189 : Blo 1156638 14084189 := bstep (se 3 (by rfl) ⟨2640785, by rfl⟩ : syracuseStep 14084189 = 5281571) B5281571
theorem B8349875 : Blo 1156638 8349875 := bstep (se 1 (by rfl) ⟨6262406, by rfl⟩ : syracuseStep 8349875 = 12524813) B12524813
theorem B1304779 : Blo 1156638 1304779 := bstep (se 1 (by rfl) ⟨978584, by rfl⟩ : syracuseStep 1304779 = 1957169) B1957169
theorem B1468631 : Blo 1156638 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B8808749 : Blo 1156638 8808749 := bstep (se 3 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 8808749 = 3303281) B3303281
theorem B1304887 : Blo 1156638 1304887 := bstep (se 1 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 1304887 = 1957331) B1957331
theorem B2091353 : Blo 1156638 2091353 := bstep (se 2 (by rfl) ⟨784257, by rfl⟩ : syracuseStep 2091353 = 1568515) B1568515
theorem B1337719 : Blo 1156638 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B8350103 : Blo 1156638 8350103 := bstep (se 1 (by rfl) ⟨6262577, by rfl⟩ : syracuseStep 8350103 = 12525155) B12525155
theorem B2779571 : Blo 1156638 2779571 := bstep (se 1 (by rfl) ⟨2084678, by rfl⟩ : syracuseStep 2779571 = 4169357) B4169357
theorem B1305067 : Blo 1156638 1305067 := bstep (se 1 (by rfl) ⟨978800, by rfl⟩ : syracuseStep 1305067 = 1957601) B1957601
theorem B1305175 : Blo 1156638 1305175 := bstep (se 1 (by rfl) ⟨978881, by rfl⟩ : syracuseStep 1305175 = 1957763) B1957763
theorem B1305355 : Blo 1156638 1305355 := bstep (se 1 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 1305355 = 1958033) B1958033
theorem B1305463 : Blo 1156638 1305463 := bstep (se 1 (by rfl) ⟨979097, by rfl⟩ : syracuseStep 1305463 = 1958195) B1958195
theorem B1305643 : Blo 1156638 1305643 := bstep (se 1 (by rfl) ⟨979232, by rfl⟩ : syracuseStep 1305643 = 1958465) B1958465
theorem B5565505 : Blo 1156638 5565505 := bstep (se 2 (by rfl) ⟨2087064, by rfl⟩ : syracuseStep 5565505 = 4174129) B4174129
theorem B32107589 : Blo 1156638 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B4943065 : Blo 1156638 4943065 := bstep (se 2 (by rfl) ⟨1853649, by rfl⟩ : syracuseStep 4943065 = 3707299) B3707299
theorem B22605101 : Blo 1156638 22605101 := bstep (se 3 (by rfl) ⟨4238456, by rfl⟩ : syracuseStep 22605101 = 8476913) B8476913
theorem B5860673 : Blo 1156638 5860673 := bstep (se 2 (by rfl) ⟨2197752, by rfl⟩ : syracuseStep 5860673 = 4395505) B4395505
theorem B5009069 : Blo 1156638 5009069 := bstep (se 3 (by rfl) ⟨939200, by rfl⟩ : syracuseStep 5009069 = 1878401) B1878401
theorem B2780993 : Blo 1156638 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B16674659 : Blo 1156638 16674659 := bstep (se 1 (by rfl) ⟨12505994, by rfl⟩ : syracuseStep 16674659 = 25011989) B25011989
theorem B4944023 : Blo 1156638 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B63336973 : Blo 1156638 63336973 := bstep (se 3 (by rfl) ⟨11875682, by rfl⟩ : syracuseStep 63336973 = 23751365) B23751365
theorem B1176151 : Blo 1156638 1176151 := bstep (se 1 (by rfl) ⟨882113, by rfl⟩ : syracuseStep 1176151 = 1764227) B1764227
theorem B28177217 : Blo 1156638 28177217 := bstep (se 2 (by rfl) ⟨10566456, by rfl⟩ : syracuseStep 28177217 = 21132913) B21132913
theorem B6681419 : Blo 1156638 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B5862617 : Blo 1156638 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B9893441 : Blo 1156638 9893441 := bstep (se 2 (by rfl) ⟨3710040, by rfl⟩ : syracuseStep 9893441 = 7420081) B7420081
theorem B10024541 : Blo 1156638 10024541 := bstep (se 3 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 10024541 = 3759203) B3759203
theorem B10581853 : Blo 1156638 10581853 := bstep (se 3 (by rfl) ⟨1984097, by rfl⟩ : syracuseStep 10581853 = 3968195) B3968195
theorem B35682227 : Blo 1156638 35682227 := bstep (se 1 (by rfl) ⟨26761670, by rfl⟩ : syracuseStep 35682227 = 53523341) B53523341
theorem B8812637 : Blo 1156638 8812637 := bstep (se 3 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 8812637 = 3304739) B3304739
theorem B2291915 : Blo 1156638 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B1735001 : Blo 1156638 1735001 := bstep (se 2 (by rfl) ⟨650625, by rfl⟩ : syracuseStep 1735001 = 1301251) B1301251
theorem B36108661 : Blo 1156638 36108661 := bstep (se 5 (by rfl) ⟨1692593, by rfl⟩ : syracuseStep 36108661 = 3385187) B3385187
theorem B1735115 : Blo 1156638 1735115 := bstep (se 1 (by rfl) ⟨1301336, by rfl⟩ : syracuseStep 1735115 = 2602673) B2602673
theorem B1735127 : Blo 1156638 1735127 := bstep (se 1 (by rfl) ⟨1301345, by rfl⟩ : syracuseStep 1735127 = 2602691) B2602691
theorem B1735193 : Blo 1156638 1735193 := bstep (se 2 (by rfl) ⟨650697, by rfl⟩ : syracuseStep 1735193 = 1301395) B1301395
theorem B1735307 : Blo 1156638 1735307 := bstep (se 1 (by rfl) ⟨1301480, by rfl⟩ : syracuseStep 1735307 = 2602961) B2602961
theorem B1735319 : Blo 1156638 1735319 := bstep (se 1 (by rfl) ⟨1301489, by rfl⟩ : syracuseStep 1735319 = 2602979) B2602979
theorem B1669835 : Blo 1156638 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1735385 : Blo 1156638 1735385 := bstep (se 2 (by rfl) ⟨650769, by rfl⟩ : syracuseStep 1735385 = 1301539) B1301539
theorem B5864237 : Blo 1156638 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B1735499 : Blo 1156638 1735499 := bstep (se 1 (by rfl) ⟨1301624, by rfl⟩ : syracuseStep 1735499 = 2603249) B2603249
theorem B1735511 : Blo 1156638 1735511 := bstep (se 1 (by rfl) ⟨1301633, by rfl⟩ : syracuseStep 1735511 = 2603267) B2603267
theorem B1735577 : Blo 1156638 1735577 := bstep (se 2 (by rfl) ⟨650841, by rfl⟩ : syracuseStep 1735577 = 1301683) B1301683
theorem B1735691 : Blo 1156638 1735691 := bstep (se 1 (by rfl) ⟨1301768, by rfl⟩ : syracuseStep 1735691 = 2603537) B2603537
theorem B1735703 : Blo 1156638 1735703 := bstep (se 1 (by rfl) ⟨1301777, by rfl⟩ : syracuseStep 1735703 = 2603555) B2603555
theorem B1735769 : Blo 1156638 1735769 := bstep (se 2 (by rfl) ⟨650913, by rfl⟩ : syracuseStep 1735769 = 1301827) B1301827
theorem B1735883 : Blo 1156638 1735883 := bstep (se 1 (by rfl) ⟨1301912, by rfl⟩ : syracuseStep 1735883 = 2603825) B2603825
theorem B1735895 : Blo 1156638 1735895 := bstep (se 1 (by rfl) ⟨1301921, by rfl⟩ : syracuseStep 1735895 = 2603843) B2603843
theorem B2784473 : Blo 1156638 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B1735961 : Blo 1156638 1735961 := bstep (se 2 (by rfl) ⟨650985, by rfl⟩ : syracuseStep 1735961 = 1301971) B1301971
theorem B1736075 : Blo 1156638 1736075 := bstep (se 1 (by rfl) ⟨1302056, by rfl⟩ : syracuseStep 1736075 = 2604113) B2604113
theorem B1736087 : Blo 1156638 1736087 := bstep (se 1 (by rfl) ⟨1302065, by rfl⟩ : syracuseStep 1736087 = 2604131) B2604131
theorem B1736153 : Blo 1156638 1736153 := bstep (se 2 (by rfl) ⟨651057, by rfl⟩ : syracuseStep 1736153 = 1302115) B1302115
theorem B4947473 : Blo 1156638 4947473 := bstep (se 2 (by rfl) ⟨1855302, by rfl⟩ : syracuseStep 4947473 = 3710605) B3710605
theorem B10157633 : Blo 1156638 10157633 := bstep (se 2 (by rfl) ⟨3809112, by rfl⟩ : syracuseStep 10157633 = 7618225) B7618225
theorem B1736267 : Blo 1156638 1736267 := bstep (se 1 (by rfl) ⟨1302200, by rfl⟩ : syracuseStep 1736267 = 2604401) B2604401
theorem B1736279 : Blo 1156638 1736279 := bstep (se 1 (by rfl) ⟨1302209, by rfl⟩ : syracuseStep 1736279 = 2604419) B2604419
theorem B1736345 : Blo 1156638 1736345 := bstep (se 2 (by rfl) ⟨651129, by rfl⟩ : syracuseStep 1736345 = 1302259) B1302259
theorem B1736459 : Blo 1156638 1736459 := bstep (se 1 (by rfl) ⟨1302344, by rfl⟩ : syracuseStep 1736459 = 2604689) B2604689
theorem B1736471 : Blo 1156638 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B1736537 : Blo 1156638 1736537 := bstep (se 2 (by rfl) ⟨651201, by rfl⟩ : syracuseStep 1736537 = 1302403) B1302403
theorem B1736651 : Blo 1156638 1736651 := bstep (se 1 (by rfl) ⟨1302488, by rfl⟩ : syracuseStep 1736651 = 2604977) B2604977
theorem B1736663 : Blo 1156638 1736663 := bstep (se 1 (by rfl) ⟨1302497, by rfl⟩ : syracuseStep 1736663 = 2604995) B2604995
theorem B1736711 : Blo 1156638 1736711 := bstep (se 1 (by rfl) ⟨1302533, by rfl⟩ : syracuseStep 1736711 = 2605067) B2605067
theorem B1736747 : Blo 1156638 1736747 := bstep (se 1 (by rfl) ⟨1302560, by rfl⟩ : syracuseStep 1736747 = 2605121) B2605121
theorem B5865533 : Blo 1156638 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B1736777 : Blo 1156638 1736777 := bstep (se 2 (by rfl) ⟨651291, by rfl⟩ : syracuseStep 1736777 = 1302583) B1302583
theorem B2785367 : Blo 1156638 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B3571859 : Blo 1156638 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B1736891 : Blo 1156638 1736891 := bstep (se 1 (by rfl) ⟨1302668, by rfl⟩ : syracuseStep 1736891 = 2605337) B2605337
theorem B1736951 : Blo 1156638 1736951 := bstep (se 1 (by rfl) ⟨1302713, by rfl⟩ : syracuseStep 1736951 = 2605427) B2605427
theorem B1736975 : Blo 1156638 1736975 := bstep (se 1 (by rfl) ⟨1302731, by rfl⟩ : syracuseStep 1736975 = 2605463) B2605463
theorem B1737017 : Blo 1156638 1737017 := bstep (se 2 (by rfl) ⟨651381, by rfl⟩ : syracuseStep 1737017 = 1302763) B1302763
theorem B1737095 : Blo 1156638 1737095 := bstep (se 1 (by rfl) ⟨1302821, by rfl⟩ : syracuseStep 1737095 = 2605643) B2605643
theorem B8356243 : Blo 1156638 8356243 := bstep (se 1 (by rfl) ⟨6267182, by rfl⟩ : syracuseStep 8356243 = 12534365) B12534365
theorem B1737131 : Blo 1156638 1737131 := bstep (se 1 (by rfl) ⟨1302848, by rfl⟩ : syracuseStep 1737131 = 2605697) B2605697
theorem B1737161 : Blo 1156638 1737161 := bstep (se 2 (by rfl) ⟨651435, by rfl⟩ : syracuseStep 1737161 = 1302871) B1302871
theorem B19792349 : Blo 1156638 19792349 := bstep (se 3 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 19792349 = 7422131) B7422131
theorem B1737275 : Blo 1156638 1737275 := bstep (se 1 (by rfl) ⟨1302956, by rfl⟩ : syracuseStep 1737275 = 2605913) B2605913
theorem B1737335 : Blo 1156638 1737335 := bstep (se 1 (by rfl) ⟨1303001, by rfl⟩ : syracuseStep 1737335 = 2606003) B2606003
theorem B1737359 : Blo 1156638 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B1737401 : Blo 1156638 1737401 := bstep (se 2 (by rfl) ⟨651525, by rfl⟩ : syracuseStep 1737401 = 1303051) B1303051
theorem B7045861 : Blo 1156638 7045861 := bstep (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) B1321099
theorem B8913665 : Blo 1156638 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B1737479 : Blo 1156638 1737479 := bstep (se 1 (by rfl) ⟨1303109, by rfl⟩ : syracuseStep 1737479 = 2606219) B2606219
theorem B1737515 : Blo 1156638 1737515 := bstep (se 1 (by rfl) ⟨1303136, by rfl⟩ : syracuseStep 1737515 = 2606273) B2606273
theorem B1737545 : Blo 1156638 1737545 := bstep (se 2 (by rfl) ⟨651579, by rfl⟩ : syracuseStep 1737545 = 1303159) B1303159
theorem B6259571 : Blo 1156638 6259571 := bstep (se 1 (by rfl) ⟨4694678, by rfl⟩ : syracuseStep 6259571 = 9389357) B9389357
theorem B5571443 : Blo 1156638 5571443 := bstep (se 1 (by rfl) ⟨4178582, by rfl⟩ : syracuseStep 5571443 = 8357165) B8357165
theorem B2196371 : Blo 1156638 2196371 := bstep (se 1 (by rfl) ⟨1647278, by rfl⟩ : syracuseStep 2196371 = 3294557) B3294557
theorem B2196409 : Blo 1156638 2196409 := bstep (se 2 (by rfl) ⟨823653, by rfl⟩ : syracuseStep 2196409 = 1647307) B1647307
theorem B1737659 : Blo 1156638 1737659 := bstep (se 1 (by rfl) ⟨1303244, by rfl⟩ : syracuseStep 1737659 = 2606489) B2606489
theorem B1737719 : Blo 1156638 1737719 := bstep (se 1 (by rfl) ⟨1303289, by rfl⟩ : syracuseStep 1737719 = 2606579) B2606579
theorem B1737743 : Blo 1156638 1737743 := bstep (se 1 (by rfl) ⟨1303307, by rfl⟩ : syracuseStep 1737743 = 2606615) B2606615
theorem B1737785 : Blo 1156638 1737785 := bstep (se 2 (by rfl) ⟨651669, by rfl⟩ : syracuseStep 1737785 = 1303339) B1303339
theorem B1737863 : Blo 1156638 1737863 := bstep (se 1 (by rfl) ⟨1303397, by rfl⟩ : syracuseStep 1737863 = 2606795) B2606795
theorem B1737899 : Blo 1156638 1737899 := bstep (se 1 (by rfl) ⟨1303424, by rfl⟩ : syracuseStep 1737899 = 2606849) B2606849
theorem B1737929 : Blo 1156638 1737929 := bstep (se 2 (by rfl) ⟨651723, by rfl⟩ : syracuseStep 1737929 = 1303447) B1303447
theorem B1738043 : Blo 1156638 1738043 := bstep (se 1 (by rfl) ⟨1303532, by rfl⟩ : syracuseStep 1738043 = 2607065) B2607065
theorem B1738103 : Blo 1156638 1738103 := bstep (se 1 (by rfl) ⟨1303577, by rfl⟩ : syracuseStep 1738103 = 2607155) B2607155
theorem B1738127 : Blo 1156638 1738127 := bstep (se 1 (by rfl) ⟨1303595, by rfl⟩ : syracuseStep 1738127 = 2607191) B2607191
theorem B4392377 : Blo 1156638 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B1738169 : Blo 1156638 1738169 := bstep (se 2 (by rfl) ⟨651813, by rfl⟩ : syracuseStep 1738169 = 1303627) B1303627
theorem B1738247 : Blo 1156638 1738247 := bstep (se 1 (by rfl) ⟨1303685, by rfl⟩ : syracuseStep 1738247 = 2607371) B2607371
theorem B1738283 : Blo 1156638 1738283 := bstep (se 1 (by rfl) ⟨1303712, by rfl⟩ : syracuseStep 1738283 = 2607425) B2607425
theorem B1738313 : Blo 1156638 1738313 := bstep (se 2 (by rfl) ⟨651867, by rfl⟩ : syracuseStep 1738313 = 1303735) B1303735
theorem B1738427 : Blo 1156638 1738427 := bstep (se 1 (by rfl) ⟨1303820, by rfl⟩ : syracuseStep 1738427 = 2607641) B2607641
theorem B5572289 : Blo 1156638 5572289 := bstep (se 2 (by rfl) ⟨2089608, by rfl⟩ : syracuseStep 5572289 = 4179217) B4179217
theorem B42239717 : Blo 1156638 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B1738487 : Blo 1156638 1738487 := bstep (se 1 (by rfl) ⟨1303865, by rfl⟩ : syracuseStep 1738487 = 2607731) B2607731
theorem B1738511 : Blo 1156638 1738511 := bstep (se 1 (by rfl) ⟨1303883, by rfl⟩ : syracuseStep 1738511 = 2607767) B2607767
theorem B2819873 : Blo 1156638 2819873 := bstep (se 2 (by rfl) ⟨1057452, by rfl⟩ : syracuseStep 2819873 = 2114905) B2114905
theorem B5867315 : Blo 1156638 5867315 := bstep (se 1 (by rfl) ⟨4400486, by rfl⟩ : syracuseStep 5867315 = 8800973) B8800973
theorem B1738553 : Blo 1156638 1738553 := bstep (se 2 (by rfl) ⟨651957, by rfl⟩ : syracuseStep 1738553 = 1303915) B1303915
theorem B1738631 : Blo 1156638 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B1738667 : Blo 1156638 1738667 := bstep (se 1 (by rfl) ⟨1304000, by rfl⟩ : syracuseStep 1738667 = 2608001) B2608001
theorem B1738697 : Blo 1156638 1738697 := bstep (se 2 (by rfl) ⟨652011, by rfl⟩ : syracuseStep 1738697 = 1304023) B1304023
theorem B6686723 : Blo 1156638 6686723 := bstep (se 1 (by rfl) ⟨5015042, by rfl⟩ : syracuseStep 6686723 = 10030085) B10030085
theorem B5572637 : Blo 1156638 5572637 := bstep (se 3 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 5572637 = 2089739) B2089739
theorem B1738811 : Blo 1156638 1738811 := bstep (se 1 (by rfl) ⟨1304108, by rfl⟩ : syracuseStep 1738811 = 2608217) B2608217
theorem B4458557 : Blo 1156638 4458557 := bstep (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) B1671959
theorem B5867639 : Blo 1156638 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1738871 : Blo 1156638 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B1738895 : Blo 1156638 1738895 := bstep (se 1 (by rfl) ⟨1304171, by rfl⟩ : syracuseStep 1738895 = 2608343) B2608343
theorem B1738937 : Blo 1156638 1738937 := bstep (se 2 (by rfl) ⟨652101, by rfl⟩ : syracuseStep 1738937 = 1304203) B1304203
theorem B2787529 : Blo 1156638 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B1739015 : Blo 1156638 1739015 := bstep (se 1 (by rfl) ⟨1304261, by rfl⟩ : syracuseStep 1739015 = 2608523) B2608523
theorem B1739051 : Blo 1156638 1739051 := bstep (se 1 (by rfl) ⟨1304288, by rfl⟩ : syracuseStep 1739051 = 2608577) B2608577
theorem B1411387 : Blo 1156638 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B1739081 : Blo 1156638 1739081 := bstep (se 2 (by rfl) ⟨652155, by rfl⟩ : syracuseStep 1739081 = 1304311) B1304311
theorem B1739195 : Blo 1156638 1739195 := bstep (se 1 (by rfl) ⟨1304396, by rfl⟩ : syracuseStep 1739195 = 2608793) B2608793
theorem B1739255 : Blo 1156638 1739255 := bstep (se 1 (by rfl) ⟨1304441, by rfl⟩ : syracuseStep 1739255 = 2608883) B2608883
theorem B1739279 : Blo 1156638 1739279 := bstep (se 1 (by rfl) ⟨1304459, by rfl⟩ : syracuseStep 1739279 = 2608919) B2608919
theorem B1739321 : Blo 1156638 1739321 := bstep (se 2 (by rfl) ⟨652245, by rfl⟩ : syracuseStep 1739321 = 1304491) B1304491
theorem B16943681 : Blo 1156638 16943681 := bstep (se 2 (by rfl) ⟨6353880, by rfl⟩ : syracuseStep 16943681 = 12707761) B12707761
theorem B1739399 : Blo 1156638 1739399 := bstep (se 1 (by rfl) ⟨1304549, by rfl⟩ : syracuseStep 1739399 = 2609099) B2609099
theorem B1739435 : Blo 1156638 1739435 := bstep (se 1 (by rfl) ⟨1304576, by rfl⟩ : syracuseStep 1739435 = 2609153) B2609153
theorem B1739465 : Blo 1156638 1739465 := bstep (se 2 (by rfl) ⟨652299, by rfl⟩ : syracuseStep 1739465 = 1304599) B1304599
theorem B16714511 : Blo 1156638 16714511 := bstep (se 1 (by rfl) ⟨12535883, by rfl⟩ : syracuseStep 16714511 = 25071767) B25071767
theorem B2198315 : Blo 1156638 2198315 := bstep (se 1 (by rfl) ⟨1648736, by rfl⟩ : syracuseStep 2198315 = 3297473) B3297473
theorem B3705659 : Blo 1156638 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B1739579 : Blo 1156638 1739579 := bstep (se 1 (by rfl) ⟨1304684, by rfl⟩ : syracuseStep 1739579 = 2609369) B2609369
theorem B76319603 : Blo 1156638 76319603 := bstep (se 1 (by rfl) ⟨57239702, by rfl⟩ : syracuseStep 76319603 = 114479405) B114479405
theorem B1739639 : Blo 1156638 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B1739663 : Blo 1156638 1739663 := bstep (se 1 (by rfl) ⟨1304747, by rfl⟩ : syracuseStep 1739663 = 2609495) B2609495
theorem B1739705 : Blo 1156638 1739705 := bstep (se 2 (by rfl) ⟨652389, by rfl⟩ : syracuseStep 1739705 = 1304779) B1304779
theorem B5082065 : Blo 1156638 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B1739783 : Blo 1156638 1739783 := bstep (se 1 (by rfl) ⟨1304837, by rfl⟩ : syracuseStep 1739783 = 2609675) B2609675
theorem B1739819 : Blo 1156638 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B5868611 : Blo 1156638 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B1739849 : Blo 1156638 1739849 := bstep (se 2 (by rfl) ⟨652443, by rfl⟩ : syracuseStep 1739849 = 1304887) B1304887
theorem B12881029 : Blo 1156638 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B6589613 : Blo 1156638 6589613 := bstep (se 3 (by rfl) ⟨1235552, by rfl⟩ : syracuseStep 6589613 = 2471105) B2471105
theorem B1739963 : Blo 1156638 1739963 := bstep (se 1 (by rfl) ⟨1304972, by rfl⟩ : syracuseStep 1739963 = 2609945) B2609945
theorem B1740023 : Blo 1156638 1740023 := bstep (se 1 (by rfl) ⟨1305017, by rfl⟩ : syracuseStep 1740023 = 2610035) B2610035
theorem B1740047 : Blo 1156638 1740047 := bstep (se 1 (by rfl) ⟨1305035, by rfl⟩ : syracuseStep 1740047 = 2610071) B2610071
theorem B1740089 : Blo 1156638 1740089 := bstep (se 2 (by rfl) ⟨652533, by rfl⟩ : syracuseStep 1740089 = 1305067) B1305067
theorem B5868935 : Blo 1156638 5868935 := bstep (se 1 (by rfl) ⟨4401701, by rfl⟩ : syracuseStep 5868935 = 8803403) B8803403
theorem B1740167 : Blo 1156638 1740167 := bstep (se 1 (by rfl) ⟨1305125, by rfl⟩ : syracuseStep 1740167 = 2610251) B2610251
theorem B1740203 : Blo 1156638 1740203 := bstep (se 1 (by rfl) ⟨1305152, by rfl⟩ : syracuseStep 1740203 = 2610305) B2610305
theorem B1740233 : Blo 1156638 1740233 := bstep (se 2 (by rfl) ⟨652587, by rfl⟩ : syracuseStep 1740233 = 1305175) B1305175
theorem B4951505 : Blo 1156638 4951505 := bstep (se 2 (by rfl) ⟨1856814, by rfl⟩ : syracuseStep 4951505 = 3713629) B3713629
theorem B1740347 : Blo 1156638 1740347 := bstep (se 1 (by rfl) ⟨1305260, by rfl⟩ : syracuseStep 1740347 = 2610521) B2610521
theorem B1740407 : Blo 1156638 1740407 := bstep (se 1 (by rfl) ⟨1305305, by rfl⟩ : syracuseStep 1740407 = 2610611) B2610611
theorem B1412743 : Blo 1156638 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1740431 : Blo 1156638 1740431 := bstep (se 1 (by rfl) ⟨1305323, by rfl⟩ : syracuseStep 1740431 = 2610647) B2610647
theorem B1740473 : Blo 1156638 1740473 := bstep (se 2 (by rfl) ⟨652677, by rfl⟩ : syracuseStep 1740473 = 1305355) B1305355
theorem B2199241 : Blo 1156638 2199241 := bstep (se 2 (by rfl) ⟨824715, by rfl⟩ : syracuseStep 2199241 = 1649431) B1649431
theorem B1740551 : Blo 1156638 1740551 := bstep (se 1 (by rfl) ⟨1305413, by rfl⟩ : syracuseStep 1740551 = 2610827) B2610827
theorem B1740587 : Blo 1156638 1740587 := bstep (se 1 (by rfl) ⟨1305440, by rfl⟩ : syracuseStep 1740587 = 2610881) B2610881
theorem B1740617 : Blo 1156638 1740617 := bstep (se 2 (by rfl) ⟨652731, by rfl⟩ : syracuseStep 1740617 = 1305463) B1305463
theorem B1740731 : Blo 1156638 1740731 := bstep (se 1 (by rfl) ⟨1305548, by rfl⟩ : syracuseStep 1740731 = 2611097) B2611097
theorem B1740791 : Blo 1156638 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B4395019 : Blo 1156638 4395019 := bstep (se 1 (by rfl) ⟨3296264, by rfl⟩ : syracuseStep 4395019 = 6592529) B6592529
theorem B1740815 : Blo 1156638 1740815 := bstep (se 1 (by rfl) ⟨1305611, by rfl⟩ : syracuseStep 1740815 = 2611223) B2611223
theorem B1740857 : Blo 1156638 1740857 := bstep (se 2 (by rfl) ⟨652821, by rfl⟩ : syracuseStep 1740857 = 1305643) B1305643
theorem B1740935 : Blo 1156638 1740935 := bstep (se 1 (by rfl) ⟨1305701, by rfl⟩ : syracuseStep 1740935 = 2611403) B2611403
theorem B6590753 : Blo 1156638 6590753 := bstep (se 2 (by rfl) ⟨2471532, by rfl⟩ : syracuseStep 6590753 = 4943065) B4943065
theorem B4395323 : Blo 1156638 4395323 := bstep (se 1 (by rfl) ⟨3296492, by rfl⟩ : syracuseStep 4395323 = 6592985) B6592985
theorem B2199955 : Blo 1156638 2199955 := bstep (se 1 (by rfl) ⟨1649966, by rfl⟩ : syracuseStep 2199955 = 3299933) B3299933
theorem B3903929 : Blo 1156638 3903929 := bstep (se 2 (by rfl) ⟨1463973, by rfl⟩ : syracuseStep 3903929 = 2927947) B2927947
theorem B4395809 : Blo 1156638 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B192779189 : Blo 1156638 192779189 := bstep (se 5 (by rfl) ⟨9036524, by rfl⟩ : syracuseStep 192779189 = 18073049) B18073049
theorem B3904523 : Blo 1156638 3904523 := bstep (se 1 (by rfl) ⟨2928392, by rfl⟩ : syracuseStep 3904523 = 5856785) B5856785
theorem B3904631 : Blo 1156638 3904631 := bstep (se 1 (by rfl) ⟨2928473, by rfl⟩ : syracuseStep 3904631 = 5856947) B5856947
theorem B2201033 : Blo 1156638 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B7050871 : Blo 1156638 7050871 := bstep (se 1 (by rfl) ⟨5288153, by rfl⟩ : syracuseStep 7050871 = 10576307) B10576307
theorem B3905225 : Blo 1156638 3905225 := bstep (se 2 (by rfl) ⟨1464459, by rfl⟩ : syracuseStep 3905225 = 2928919) B2928919
theorem B4396781 : Blo 1156638 4396781 := bstep (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) B1648793
theorem B84449297 : Blo 1156638 84449297 := bstep (se 2 (by rfl) ⟨31668486, by rfl⟩ : syracuseStep 84449297 = 63336973) B63336973
theorem B39688309 : Blo 1156638 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B5576941 : Blo 1156638 5576941 := bstep (se 3 (by rfl) ⟨1045676, by rfl⟩ : syracuseStep 5576941 = 2091353) B2091353
theorem B2201899 : Blo 1156638 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B106928437 : Blo 1156638 106928437 := bstep (se 5 (by rfl) ⟨5012270, by rfl⟩ : syracuseStep 106928437 = 10024541) B10024541
theorem B2201975 : Blo 1156638 2201975 := bstep (se 1 (by rfl) ⟨1651481, by rfl⟩ : syracuseStep 2201975 = 3302963) B3302963
theorem B3905927 : Blo 1156638 3905927 := bstep (se 1 (by rfl) ⟨2929445, by rfl⟩ : syracuseStep 3905927 = 5858891) B5858891
theorem B3906305 : Blo 1156638 3906305 := bstep (se 2 (by rfl) ⟨1464864, by rfl⟩ : syracuseStep 3906305 = 2929729) B2929729
theorem B11279179 : Blo 1156638 11279179 := bstep (se 1 (by rfl) ⟨8459384, by rfl⟩ : syracuseStep 11279179 = 16918769) B16918769
theorem B19766105 : Blo 1156638 19766105 := bstep (se 2 (by rfl) ⟨7412289, by rfl⟩ : syracuseStep 19766105 = 14824579) B14824579
theorem B5872499 : Blo 1156638 5872499 := bstep (se 1 (by rfl) ⟨4404374, by rfl⟩ : syracuseStep 5872499 = 8808749) B8808749
theorem B5872985 : Blo 1156638 5872985 := bstep (se 2 (by rfl) ⟨2202369, by rfl⟩ : syracuseStep 5872985 = 4404739) B4404739
theorem B21405059 : Blo 1156638 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B3907115 : Blo 1156638 3907115 := bstep (se 1 (by rfl) ⟨2930336, by rfl⟩ : syracuseStep 3907115 = 5860673) B5860673
theorem B4398907 : Blo 1156638 4398907 := bstep (se 1 (by rfl) ⟨3299180, by rfl⟩ : syracuseStep 4398907 = 6598361) B6598361
theorem B11116439 : Blo 1156638 11116439 := bstep (se 1 (by rfl) ⟨8337329, by rfl⟩ : syracuseStep 11116439 = 16674659) B16674659
theorem B4956221 : Blo 1156638 4956221 := bstep (se 3 (by rfl) ⟨929291, by rfl⟩ : syracuseStep 4956221 = 1858583) B1858583
theorem B4399393 : Blo 1156638 4399393 := bstep (se 2 (by rfl) ⟨1649772, by rfl⟩ : syracuseStep 4399393 = 3299545) B3299545
theorem B48144881 : Blo 1156638 48144881 := bstep (se 2 (by rfl) ⟨18054330, by rfl⟩ : syracuseStep 48144881 = 36108661) B36108661
theorem B18784811 : Blo 1156638 18784811 := bstep (se 1 (by rfl) ⟨14088608, by rfl⟩ : syracuseStep 18784811 = 28177217) B28177217
theorem B14099021 : Blo 1156638 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B3908411 : Blo 1156638 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B1647631 : Blo 1156638 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B6595627 : Blo 1156638 6595627 := bstep (se 1 (by rfl) ⟨4946720, by rfl⟩ : syracuseStep 6595627 = 9893441) B9893441
theorem B1320079 : Blo 1156638 1320079 := bstep (se 1 (by rfl) ⟨990059, by rfl⟩ : syracuseStep 1320079 = 1980119) B1980119
theorem B4400365 : Blo 1156638 4400365 := bstep (se 3 (by rfl) ⟨825068, by rfl⟩ : syracuseStep 4400365 = 1650137) B1650137
theorem B3908897 : Blo 1156638 3908897 := bstep (se 2 (by rfl) ⟨1465836, by rfl⟩ : syracuseStep 3908897 = 2931673) B2931673
theorem B5875091 : Blo 1156638 5875091 := bstep (se 1 (by rfl) ⟨4406318, by rfl⟩ : syracuseStep 5875091 = 8812637) B8812637
theorem B4400669 : Blo 1156638 4400669 := bstep (se 3 (by rfl) ⟨825125, by rfl⟩ : syracuseStep 4400669 = 1650251) B1650251
theorem B1156667 : Blo 1156638 1156667 := bstep (se 1 (by rfl) ⟨867500, by rfl⟩ : syracuseStep 1156667 = 1735001) B1735001
theorem B1648201 : Blo 1156638 1648201 := bstep (se 2 (by rfl) ⟨618075, by rfl⟩ : syracuseStep 1648201 = 1236151) B1236151
theorem B1156743 : Blo 1156638 1156743 := bstep (se 1 (by rfl) ⟨867557, by rfl⟩ : syracuseStep 1156743 = 1735115) B1735115
theorem B1156751 : Blo 1156638 1156751 := bstep (se 1 (by rfl) ⟨867563, by rfl⟩ : syracuseStep 1156751 = 1735127) B1735127
theorem B1156795 : Blo 1156638 1156795 := bstep (se 1 (by rfl) ⟨867596, by rfl⟩ : syracuseStep 1156795 = 1735193) B1735193
theorem B1156871 : Blo 1156638 1156871 := bstep (se 1 (by rfl) ⟨867653, by rfl⟩ : syracuseStep 1156871 = 1735307) B1735307
theorem B1156879 : Blo 1156638 1156879 := bstep (se 1 (by rfl) ⟨867659, by rfl⟩ : syracuseStep 1156879 = 1735319) B1735319
theorem B1156923 : Blo 1156638 1156923 := bstep (se 1 (by rfl) ⟨867692, by rfl⟩ : syracuseStep 1156923 = 1735385) B1735385
theorem B3909491 : Blo 1156638 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B1156999 : Blo 1156638 1156999 := bstep (se 1 (by rfl) ⟨867749, by rfl⟩ : syracuseStep 1156999 = 1735499) B1735499
theorem B1157007 : Blo 1156638 1157007 := bstep (se 1 (by rfl) ⟨867755, by rfl⟩ : syracuseStep 1157007 = 1735511) B1735511
theorem B1157051 : Blo 1156638 1157051 := bstep (se 1 (by rfl) ⟨867788, by rfl⟩ : syracuseStep 1157051 = 1735577) B1735577
theorem B1157127 : Blo 1156638 1157127 := bstep (se 1 (by rfl) ⟨867845, by rfl⟩ : syracuseStep 1157127 = 1735691) B1735691
theorem B1157135 : Blo 1156638 1157135 := bstep (se 1 (by rfl) ⟨867851, by rfl⟩ : syracuseStep 1157135 = 1735703) B1735703
theorem B1157179 : Blo 1156638 1157179 := bstep (se 1 (by rfl) ⟨867884, by rfl⟩ : syracuseStep 1157179 = 1735769) B1735769
theorem B1157255 : Blo 1156638 1157255 := bstep (se 1 (by rfl) ⟨867941, by rfl⟩ : syracuseStep 1157255 = 1735883) B1735883
theorem B1157263 : Blo 1156638 1157263 := bstep (se 1 (by rfl) ⟨867947, by rfl⟩ : syracuseStep 1157263 = 1735895) B1735895
theorem B7415981 : Blo 1156638 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B1157307 : Blo 1156638 1157307 := bstep (se 1 (by rfl) ⟨867980, by rfl⟩ : syracuseStep 1157307 = 1735961) B1735961
theorem B1157383 : Blo 1156638 1157383 := bstep (se 1 (by rfl) ⟨868037, by rfl⟩ : syracuseStep 1157383 = 1736075) B1736075
theorem B1157391 : Blo 1156638 1157391 := bstep (se 1 (by rfl) ⟨868043, by rfl⟩ : syracuseStep 1157391 = 1736087) B1736087
theorem B54241589 : Blo 1156638 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B1157435 : Blo 1156638 1157435 := bstep (se 1 (by rfl) ⟨868076, by rfl⟩ : syracuseStep 1157435 = 1736153) B1736153
theorem B1157511 : Blo 1156638 1157511 := bstep (se 1 (by rfl) ⟨868133, by rfl⟩ : syracuseStep 1157511 = 1736267) B1736267
theorem B1157519 : Blo 1156638 1157519 := bstep (se 1 (by rfl) ⟨868139, by rfl⟩ : syracuseStep 1157519 = 1736279) B1736279
theorem B1157563 : Blo 1156638 1157563 := bstep (se 1 (by rfl) ⟨868172, by rfl⟩ : syracuseStep 1157563 = 1736345) B1736345
theorem B6597085 : Blo 1156638 6597085 := bstep (se 3 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 6597085 = 2473907) B2473907
theorem B1157639 : Blo 1156638 1157639 := bstep (se 1 (by rfl) ⟨868229, by rfl⟩ : syracuseStep 1157639 = 1736459) B1736459
theorem B1157647 : Blo 1156638 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B1157691 : Blo 1156638 1157691 := bstep (se 1 (by rfl) ⟨868268, by rfl⟩ : syracuseStep 1157691 = 1736537) B1736537
theorem B1157767 : Blo 1156638 1157767 := bstep (se 1 (by rfl) ⟨868325, by rfl⟩ : syracuseStep 1157767 = 1736651) B1736651
theorem B1157775 : Blo 1156638 1157775 := bstep (se 1 (by rfl) ⟨868331, by rfl⟩ : syracuseStep 1157775 = 1736663) B1736663
theorem B1157819 : Blo 1156638 1157819 := bstep (se 1 (by rfl) ⟨868364, by rfl⟩ : syracuseStep 1157819 = 1736729) B1736729
theorem B1157895 : Blo 1156638 1157895 := bstep (se 1 (by rfl) ⟨868421, by rfl⟩ : syracuseStep 1157895 = 1736843) B1736843
theorem B1157903 : Blo 1156638 1157903 := bstep (se 1 (by rfl) ⟨868427, by rfl⟩ : syracuseStep 1157903 = 1736855) B1736855
theorem B1157947 : Blo 1156638 1157947 := bstep (se 1 (by rfl) ⟨868460, by rfl⟩ : syracuseStep 1157947 = 1736921) B1736921
theorem B1158023 : Blo 1156638 1158023 := bstep (se 1 (by rfl) ⟨868517, by rfl⟩ : syracuseStep 1158023 = 1737035) B1737035
theorem B1158031 : Blo 1156638 1158031 := bstep (se 1 (by rfl) ⟨868523, by rfl⟩ : syracuseStep 1158031 = 1737047) B1737047
theorem B1158075 : Blo 1156638 1158075 := bstep (se 1 (by rfl) ⟨868556, by rfl⟩ : syracuseStep 1158075 = 1737113) B1737113
theorem B5647313 : Blo 1156638 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B1158151 : Blo 1156638 1158151 := bstep (se 1 (by rfl) ⟨868613, by rfl⟩ : syracuseStep 1158151 = 1737227) B1737227
theorem B1158159 : Blo 1156638 1158159 := bstep (se 1 (by rfl) ⟨868619, by rfl⟩ : syracuseStep 1158159 = 1737239) B1737239
theorem B1158203 : Blo 1156638 1158203 := bstep (se 1 (by rfl) ⟨868652, by rfl⟩ : syracuseStep 1158203 = 1737305) B1737305
theorem B4402295 : Blo 1156638 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B1158279 : Blo 1156638 1158279 := bstep (se 1 (by rfl) ⟨868709, by rfl⟩ : syracuseStep 1158279 = 1737419) B1737419
theorem B1158287 : Blo 1156638 1158287 := bstep (se 1 (by rfl) ⟨868715, by rfl⟩ : syracuseStep 1158287 = 1737431) B1737431
theorem B1158331 : Blo 1156638 1158331 := bstep (se 1 (by rfl) ⟨868748, by rfl⟩ : syracuseStep 1158331 = 1737497) B1737497
theorem B1158407 : Blo 1156638 1158407 := bstep (se 1 (by rfl) ⟨868805, by rfl⟩ : syracuseStep 1158407 = 1737611) B1737611
theorem B1158415 : Blo 1156638 1158415 := bstep (se 1 (by rfl) ⟨868811, by rfl⟩ : syracuseStep 1158415 = 1737623) B1737623
theorem B1158459 : Blo 1156638 1158459 := bstep (se 1 (by rfl) ⟨868844, by rfl⟩ : syracuseStep 1158459 = 1737689) B1737689
theorem B1158535 : Blo 1156638 1158535 := bstep (se 1 (by rfl) ⟨868901, by rfl⟩ : syracuseStep 1158535 = 1737803) B1737803
theorem B1158543 : Blo 1156638 1158543 := bstep (se 1 (by rfl) ⟨868907, by rfl⟩ : syracuseStep 1158543 = 1737815) B1737815
theorem B1158587 : Blo 1156638 1158587 := bstep (se 1 (by rfl) ⟨868940, by rfl⟩ : syracuseStep 1158587 = 1737881) B1737881
theorem B1158663 : Blo 1156638 1158663 := bstep (se 1 (by rfl) ⟨868997, by rfl⟩ : syracuseStep 1158663 = 1737995) B1737995
theorem B1158671 : Blo 1156638 1158671 := bstep (se 1 (by rfl) ⟨869003, by rfl⟩ : syracuseStep 1158671 = 1738007) B1738007
theorem B1158715 : Blo 1156638 1158715 := bstep (se 1 (by rfl) ⟨869036, by rfl⟩ : syracuseStep 1158715 = 1738073) B1738073
theorem B1158791 : Blo 1156638 1158791 := bstep (se 1 (by rfl) ⟨869093, by rfl⟩ : syracuseStep 1158791 = 1738187) B1738187
theorem B1158799 : Blo 1156638 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B1158843 : Blo 1156638 1158843 := bstep (se 1 (by rfl) ⟨869132, by rfl⟩ : syracuseStep 1158843 = 1738265) B1738265
theorem B11153153 : Blo 1156638 11153153 := bstep (se 2 (by rfl) ⟨4182432, by rfl⟩ : syracuseStep 11153153 = 8364865) B8364865
theorem B1158919 : Blo 1156638 1158919 := bstep (se 1 (by rfl) ⟨869189, by rfl⟩ : syracuseStep 1158919 = 1738379) B1738379
theorem B1158927 : Blo 1156638 1158927 := bstep (se 1 (by rfl) ⟨869195, by rfl⟩ : syracuseStep 1158927 = 1738391) B1738391
theorem B6696755 : Blo 1156638 6696755 := bstep (se 1 (by rfl) ⟨5022566, by rfl⟩ : syracuseStep 6696755 = 10045133) B10045133
theorem B1158971 : Blo 1156638 1158971 := bstep (se 1 (by rfl) ⟨869228, by rfl⟩ : syracuseStep 1158971 = 1738457) B1738457
theorem B1159047 : Blo 1156638 1159047 := bstep (se 1 (by rfl) ⟨869285, by rfl⟩ : syracuseStep 1159047 = 1738571) B1738571
theorem B1159055 : Blo 1156638 1159055 := bstep (se 1 (by rfl) ⟨869291, by rfl⟩ : syracuseStep 1159055 = 1738583) B1738583
theorem B35630999 : Blo 1156638 35630999 := bstep (se 1 (by rfl) ⟨26723249, by rfl⟩ : syracuseStep 35630999 = 53446499) B53446499
theorem B1159099 : Blo 1156638 1159099 := bstep (se 1 (by rfl) ⟨869324, by rfl⟩ : syracuseStep 1159099 = 1738649) B1738649
theorem B1159175 : Blo 1156638 1159175 := bstep (se 1 (by rfl) ⟨869381, by rfl⟩ : syracuseStep 1159175 = 1738763) B1738763
theorem B1159183 : Blo 1156638 1159183 := bstep (se 1 (by rfl) ⟨869387, by rfl⟩ : syracuseStep 1159183 = 1738775) B1738775
theorem B1159227 : Blo 1156638 1159227 := bstep (se 1 (by rfl) ⟨869420, by rfl⟩ : syracuseStep 1159227 = 1738841) B1738841
theorem B4403267 : Blo 1156638 4403267 := bstep (se 1 (by rfl) ⟨3302450, by rfl⟩ : syracuseStep 4403267 = 6604901) B6604901
theorem B1159303 : Blo 1156638 1159303 := bstep (se 1 (by rfl) ⟨869477, by rfl⟩ : syracuseStep 1159303 = 1738955) B1738955
theorem B1159311 : Blo 1156638 1159311 := bstep (se 1 (by rfl) ⟨869483, by rfl⟩ : syracuseStep 1159311 = 1738967) B1738967
theorem B1159355 : Blo 1156638 1159355 := bstep (se 1 (by rfl) ⟨869516, by rfl⟩ : syracuseStep 1159355 = 1739033) B1739033
theorem B1650889 : Blo 1156638 1650889 := bstep (se 2 (by rfl) ⟨619083, by rfl⟩ : syracuseStep 1650889 = 1238167) B1238167
theorem B1159431 : Blo 1156638 1159431 := bstep (se 1 (by rfl) ⟨869573, by rfl⟩ : syracuseStep 1159431 = 1739147) B1739147
theorem B1159439 : Blo 1156638 1159439 := bstep (se 1 (by rfl) ⟨869579, by rfl⟩ : syracuseStep 1159439 = 1739159) B1739159
theorem B1159483 : Blo 1156638 1159483 := bstep (se 1 (by rfl) ⟨869612, by rfl⟩ : syracuseStep 1159483 = 1739225) B1739225
theorem B6271291 : Blo 1156638 6271291 := bstep (se 1 (by rfl) ⟨4703468, by rfl⟩ : syracuseStep 6271291 = 9406937) B9406937
theorem B2929031 : Blo 1156638 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B1159559 : Blo 1156638 1159559 := bstep (se 1 (by rfl) ⟨869669, by rfl⟩ : syracuseStep 1159559 = 1739339) B1739339
theorem B3715463 : Blo 1156638 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B1159567 : Blo 1156638 1159567 := bstep (se 1 (by rfl) ⟨869675, by rfl⟩ : syracuseStep 1159567 = 1739351) B1739351
theorem B3912083 : Blo 1156638 3912083 := bstep (se 1 (by rfl) ⟨2934062, by rfl⟩ : syracuseStep 3912083 = 5868125) B5868125
theorem B2929081 : Blo 1156638 2929081 := bstep (se 2 (by rfl) ⟨1098405, by rfl⟩ : syracuseStep 2929081 = 2196811) B2196811
theorem B1159611 : Blo 1156638 1159611 := bstep (se 1 (by rfl) ⟨869708, by rfl⟩ : syracuseStep 1159611 = 1739417) B1739417
theorem B1159687 : Blo 1156638 1159687 := bstep (se 1 (by rfl) ⟨869765, by rfl⟩ : syracuseStep 1159687 = 1739531) B1739531
theorem B1159695 : Blo 1156638 1159695 := bstep (se 1 (by rfl) ⟨869771, by rfl⟩ : syracuseStep 1159695 = 1739543) B1739543
theorem B1159739 : Blo 1156638 1159739 := bstep (se 1 (by rfl) ⟨869804, by rfl⟩ : syracuseStep 1159739 = 1739609) B1739609
theorem B1880695 : Blo 1156638 1880695 := bstep (se 1 (by rfl) ⟨1410521, by rfl⟩ : syracuseStep 1880695 = 2821043) B2821043
theorem B1159815 : Blo 1156638 1159815 := bstep (se 1 (by rfl) ⟨869861, by rfl⟩ : syracuseStep 1159815 = 1739723) B1739723
theorem B1159823 : Blo 1156638 1159823 := bstep (se 1 (by rfl) ⟨869867, by rfl⟩ : syracuseStep 1159823 = 1739735) B1739735
theorem B1159867 : Blo 1156638 1159867 := bstep (se 1 (by rfl) ⟨869900, by rfl⟩ : syracuseStep 1159867 = 1739801) B1739801
theorem B1159943 : Blo 1156638 1159943 := bstep (se 1 (by rfl) ⟨869957, by rfl⟩ : syracuseStep 1159943 = 1739915) B1739915
theorem B1159951 : Blo 1156638 1159951 := bstep (se 1 (by rfl) ⟨869963, by rfl⟩ : syracuseStep 1159951 = 1739927) B1739927
theorem B1487659 : Blo 1156638 1487659 := bstep (se 1 (by rfl) ⟨1115744, by rfl⟩ : syracuseStep 1487659 = 2231489) B2231489
theorem B1159995 : Blo 1156638 1159995 := bstep (se 1 (by rfl) ⟨869996, by rfl⟩ : syracuseStep 1159995 = 1739993) B1739993
theorem B1160071 : Blo 1156638 1160071 := bstep (se 1 (by rfl) ⟨870053, by rfl⟩ : syracuseStep 1160071 = 1740107) B1740107
theorem B1160079 : Blo 1156638 1160079 := bstep (se 1 (by rfl) ⟨870059, by rfl⟩ : syracuseStep 1160079 = 1740119) B1740119
theorem B14300057 : Blo 1156638 14300057 := bstep (se 2 (by rfl) ⟨5362521, by rfl⟩ : syracuseStep 14300057 = 10725043) B10725043
theorem B1160123 : Blo 1156638 1160123 := bstep (se 1 (by rfl) ⟨870092, by rfl⟩ : syracuseStep 1160123 = 1740185) B1740185
theorem B1160199 : Blo 1156638 1160199 := bstep (se 1 (by rfl) ⟨870149, by rfl⟩ : syracuseStep 1160199 = 1740299) B1740299
theorem B2929679 : Blo 1156638 2929679 := bstep (se 1 (by rfl) ⟨2197259, by rfl⟩ : syracuseStep 2929679 = 4394519) B4394519
theorem B1160207 : Blo 1156638 1160207 := bstep (se 1 (by rfl) ⟨870155, by rfl⟩ : syracuseStep 1160207 = 1740311) B1740311
theorem B4404253 : Blo 1156638 4404253 := bstep (se 3 (by rfl) ⟨825797, by rfl⟩ : syracuseStep 4404253 = 1651595) B1651595
theorem B1160251 : Blo 1156638 1160251 := bstep (se 1 (by rfl) ⟨870188, by rfl⟩ : syracuseStep 1160251 = 1740377) B1740377
theorem B1160327 : Blo 1156638 1160327 := bstep (se 1 (by rfl) ⟨870245, by rfl⟩ : syracuseStep 1160327 = 1740491) B1740491
theorem B1160335 : Blo 1156638 1160335 := bstep (se 1 (by rfl) ⟨870251, by rfl⟩ : syracuseStep 1160335 = 1740503) B1740503
theorem B1160379 : Blo 1156638 1160379 := bstep (se 1 (by rfl) ⟨870284, by rfl⟩ : syracuseStep 1160379 = 1740569) B1740569
theorem B1160455 : Blo 1156638 1160455 := bstep (se 1 (by rfl) ⟨870341, by rfl⟩ : syracuseStep 1160455 = 1740683) B1740683
theorem B1160463 : Blo 1156638 1160463 := bstep (se 1 (by rfl) ⟨870347, by rfl⟩ : syracuseStep 1160463 = 1740695) B1740695
theorem B1160507 : Blo 1156638 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B2471303 : Blo 1156638 2471303 := bstep (se 1 (by rfl) ⟨1853477, by rfl⟩ : syracuseStep 2471303 = 3706955) B3706955
theorem B1160583 : Blo 1156638 1160583 := bstep (se 1 (by rfl) ⟨870437, by rfl⟩ : syracuseStep 1160583 = 1740875) B1740875
theorem B1160591 : Blo 1156638 1160591 := bstep (se 1 (by rfl) ⟨870443, by rfl⟩ : syracuseStep 1160591 = 1740887) B1740887
theorem B1160635 : Blo 1156638 1160635 := bstep (se 1 (by rfl) ⟨870476, by rfl⟩ : syracuseStep 1160635 = 1740953) B1740953
theorem B2602511 : Blo 1156638 2602511 := bstep (se 1 (by rfl) ⟨1951883, by rfl⟩ : syracuseStep 2602511 = 3903767) B3903767
theorem B2602529 : Blo 1156638 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B1488443 : Blo 1156638 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B6108739 : Blo 1156638 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B2930377 : Blo 1156638 2930377 := bstep (se 2 (by rfl) ⟨1098891, by rfl⟩ : syracuseStep 2930377 = 2197783) B2197783
theorem B3913487 : Blo 1156638 3913487 := bstep (se 1 (by rfl) ⟨2935115, by rfl⟩ : syracuseStep 3913487 = 5870231) B5870231
theorem B1783625 : Blo 1156638 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B2930519 : Blo 1156638 2930519 := bstep (se 1 (by rfl) ⟨2197889, by rfl⟩ : syracuseStep 2930519 = 4395779) B4395779
theorem B2602871 : Blo 1156638 2602871 := bstep (se 1 (by rfl) ⟨1952153, by rfl⟩ : syracuseStep 2602871 = 3904307) B3904307
theorem B6272977 : Blo 1156638 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B3913757 : Blo 1156638 3913757 := bstep (se 3 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 3913757 = 1467659) B1467659
theorem B2603051 : Blo 1156638 2603051 := bstep (se 1 (by rfl) ⟨1952288, by rfl⟩ : syracuseStep 2603051 = 3904577) B3904577
theorem B10729559 : Blo 1156638 10729559 := bstep (se 1 (by rfl) ⟨8047169, by rfl⟩ : syracuseStep 10729559 = 16094339) B16094339
theorem B2603411 : Blo 1156638 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B2603465 : Blo 1156638 2603465 := bstep (se 2 (by rfl) ⟨976299, by rfl⟩ : syracuseStep 2603465 = 1952599) B1952599
theorem B11123203 : Blo 1156638 11123203 := bstep (se 1 (by rfl) ⟨8342402, by rfl⟩ : syracuseStep 11123203 = 16684805) B16684805
theorem B6601277 : Blo 1156638 6601277 := bstep (se 3 (by rfl) ⟨1237739, by rfl⟩ : syracuseStep 6601277 = 2475479) B2475479
theorem B7420673 : Blo 1156638 7420673 := bstep (se 2 (by rfl) ⟨2782752, by rfl⟩ : syracuseStep 7420673 = 5565505) B5565505
theorem B2472763 : Blo 1156638 2472763 := bstep (se 1 (by rfl) ⟨1854572, by rfl⟩ : syracuseStep 2472763 = 3709145) B3709145
theorem B2473019 : Blo 1156638 2473019 := bstep (se 1 (by rfl) ⟨1854764, by rfl⟩ : syracuseStep 2473019 = 3709529) B3709529
theorem B8928317 : Blo 1156638 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B2604167 : Blo 1156638 2604167 := bstep (se 1 (by rfl) ⟨1953125, by rfl⟩ : syracuseStep 2604167 = 3906251) B3906251
theorem B6601985 : Blo 1156638 6601985 := bstep (se 2 (by rfl) ⟨2475744, by rfl⟩ : syracuseStep 6601985 = 4951489) B4951489
theorem B2604347 : Blo 1156638 2604347 := bstep (se 1 (by rfl) ⟨1953260, by rfl⟩ : syracuseStep 2604347 = 3906521) B3906521
theorem B3915161 : Blo 1156638 3915161 := bstep (se 2 (by rfl) ⟨1468185, by rfl⟩ : syracuseStep 3915161 = 2936371) B2936371
theorem B2604473 : Blo 1156638 2604473 := bstep (se 2 (by rfl) ⟨976677, by rfl⟩ : syracuseStep 2604473 = 1953355) B1953355
theorem B2604815 : Blo 1156638 2604815 := bstep (se 1 (by rfl) ⟨1953611, by rfl⟩ : syracuseStep 2604815 = 3907223) B3907223
theorem B2604833 : Blo 1156638 2604833 := bstep (se 2 (by rfl) ⟨976812, by rfl⟩ : syracuseStep 2604833 = 1953625) B1953625
theorem B2932595 : Blo 1156638 2932595 := bstep (se 1 (by rfl) ⟨2199446, by rfl⟩ : syracuseStep 2932595 = 4398893) B4398893
theorem B13189067 : Blo 1156638 13189067 := bstep (se 1 (by rfl) ⟨9891800, by rfl⟩ : syracuseStep 13189067 = 19783601) B19783601
theorem B3915863 : Blo 1156638 3915863 := bstep (se 1 (by rfl) ⟨2936897, by rfl⟩ : syracuseStep 3915863 = 5873795) B5873795
theorem B2605175 : Blo 1156638 2605175 := bstep (se 1 (by rfl) ⟨1953881, by rfl⟩ : syracuseStep 2605175 = 3907763) B3907763
theorem B2605355 : Blo 1156638 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B2933111 : Blo 1156638 2933111 := bstep (se 1 (by rfl) ⟨2199833, by rfl⟩ : syracuseStep 2933111 = 4399667) B4399667
theorem B11125201 : Blo 1156638 11125201 := bstep (se 2 (by rfl) ⟨4171950, by rfl⟩ : syracuseStep 11125201 = 8343901) B8343901
theorem B6111773 : Blo 1156638 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B3916349 : Blo 1156638 3916349 := bstep (se 3 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 3916349 = 1468631) B1468631
theorem B4702787 : Blo 1156638 4702787 := bstep (se 1 (by rfl) ⟨3527090, by rfl⟩ : syracuseStep 4702787 = 7054181) B7054181
theorem B2605715 : Blo 1156638 2605715 := bstep (se 1 (by rfl) ⟨1954286, by rfl⟩ : syracuseStep 2605715 = 3908573) B3908573
theorem B2605769 : Blo 1156638 2605769 := bstep (se 2 (by rfl) ⟨977163, by rfl⟩ : syracuseStep 2605769 = 1954327) B1954327
theorem B3294067 : Blo 1156638 3294067 := bstep (se 1 (by rfl) ⟨2470550, by rfl⟩ : syracuseStep 3294067 = 4941101) B4941101
theorem B2934103 : Blo 1156638 2934103 := bstep (se 1 (by rfl) ⟨2200577, by rfl⟩ : syracuseStep 2934103 = 4401155) B4401155
theorem B2606471 : Blo 1156638 2606471 := bstep (se 1 (by rfl) ⟨1954853, by rfl⟩ : syracuseStep 2606471 = 3909707) B3909707
theorem B9389459 : Blo 1156638 9389459 := bstep (se 1 (by rfl) ⟨7042094, by rfl⟩ : syracuseStep 9389459 = 14084189) B14084189
theorem B3130771 : Blo 1156638 3130771 := bstep (se 1 (by rfl) ⟨2348078, by rfl⟩ : syracuseStep 3130771 = 4696157) B4696157
theorem B2606651 : Blo 1156638 2606651 := bstep (se 1 (by rfl) ⟨1954988, by rfl⟩ : syracuseStep 2606651 = 3909977) B3909977
theorem B6604375 : Blo 1156638 6604375 := bstep (se 1 (by rfl) ⟨4953281, by rfl⟩ : syracuseStep 6604375 = 9906563) B9906563
theorem B1853047 : Blo 1156638 1853047 := bstep (se 1 (by rfl) ⟨1389785, by rfl⟩ : syracuseStep 1853047 = 2779571) B2779571
theorem B2934407 : Blo 1156638 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B2606777 : Blo 1156638 2606777 := bstep (se 2 (by rfl) ⟨977541, by rfl⟩ : syracuseStep 2606777 = 1955083) B1955083
theorem B8800001 : Blo 1156638 8800001 := bstep (se 2 (by rfl) ⟨3300000, by rfl⟩ : syracuseStep 8800001 = 6600001) B6600001
theorem B2934539 : Blo 1156638 2934539 := bstep (se 1 (by rfl) ⟨2200904, by rfl⟩ : syracuseStep 2934539 = 4401809) B4401809
theorem B2607119 : Blo 1156638 2607119 := bstep (se 1 (by rfl) ⟨1955339, by rfl⟩ : syracuseStep 2607119 = 3910679) B3910679
theorem B2607137 : Blo 1156638 2607137 := bstep (se 2 (by rfl) ⟨977676, by rfl⟩ : syracuseStep 2607137 = 1955353) B1955353
theorem B2935055 : Blo 1156638 2935055 := bstep (se 1 (by rfl) ⟨2201291, by rfl⟩ : syracuseStep 2935055 = 4402583) B4402583
theorem B1952059 : Blo 1156638 1952059 := bstep (se 1 (by rfl) ⟨1464044, by rfl⟩ : syracuseStep 1952059 = 2928089) B2928089
theorem B2607479 : Blo 1156638 2607479 := bstep (se 1 (by rfl) ⟨1955609, by rfl⟩ : syracuseStep 2607479 = 3911219) B3911219
theorem B2935187 : Blo 1156638 2935187 := bstep (se 1 (by rfl) ⟨2201390, by rfl⟩ : syracuseStep 2935187 = 4402781) B4402781
theorem B3295673 : Blo 1156638 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B1952201 : Blo 1156638 1952201 := bstep (se 2 (by rfl) ⟨732075, by rfl⟩ : syracuseStep 1952201 = 1464151) B1464151
theorem B14109137 : Blo 1156638 14109137 := bstep (se 2 (by rfl) ⟨5290926, by rfl⟩ : syracuseStep 14109137 = 10581853) B10581853
theorem B2607659 : Blo 1156638 2607659 := bstep (se 1 (by rfl) ⟨1955744, by rfl⟩ : syracuseStep 2607659 = 3911489) B3911489
theorem B3296015 : Blo 1156638 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B2608019 : Blo 1156638 2608019 := bstep (se 1 (by rfl) ⟨1956014, by rfl⟩ : syracuseStep 2608019 = 3912029) B3912029
theorem B2608073 : Blo 1156638 2608073 := bstep (se 2 (by rfl) ⟨978027, by rfl⟩ : syracuseStep 2608073 = 1956055) B1956055
theorem B50187275 : Blo 1156638 50187275 := bstep (se 1 (by rfl) ⟨37640456, by rfl⟩ : syracuseStep 50187275 = 75280913) B75280913
theorem B1952903 : Blo 1156638 1952903 := bstep (se 1 (by rfl) ⟨1464677, by rfl⟩ : syracuseStep 1952903 = 2929355) B2929355
theorem B2936321 : Blo 1156638 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B6606359 : Blo 1156638 6606359 := bstep (se 1 (by rfl) ⟨4954769, by rfl⟩ : syracuseStep 6606359 = 9909539) B9909539
theorem B3296801 : Blo 1156638 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B2608775 : Blo 1156638 2608775 := bstep (se 1 (by rfl) ⟨1956581, by rfl⟩ : syracuseStep 2608775 = 3913163) B3913163
theorem B8343269 : Blo 1156638 8343269 := bstep (se 4 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 8343269 = 1564363) B1564363
theorem B11128549 : Blo 1156638 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B1953551 : Blo 1156638 1953551 := bstep (se 1 (by rfl) ⟨1465163, by rfl⟩ : syracuseStep 1953551 = 2930327) B2930327
theorem B2608955 : Blo 1156638 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B2936695 : Blo 1156638 2936695 := bstep (se 1 (by rfl) ⟨2202521, by rfl⟩ : syracuseStep 2936695 = 4405043) B4405043
theorem B2609081 : Blo 1156638 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B7131089 : Blo 1156638 7131089 := bstep (se 2 (by rfl) ⟨2674158, by rfl⟩ : syracuseStep 7131089 = 5348317) B5348317
theorem B2085011 : Blo 1156638 2085011 := bstep (se 1 (by rfl) ⟨1563758, by rfl⟩ : syracuseStep 2085011 = 3127517) B3127517
theorem B2478281 : Blo 1156638 2478281 := bstep (se 2 (by rfl) ⟨929355, by rfl⟩ : syracuseStep 2478281 = 1858711) B1858711
theorem B2609423 : Blo 1156638 2609423 := bstep (se 1 (by rfl) ⟨1957067, by rfl⟩ : syracuseStep 2609423 = 3914135) B3914135
theorem B2609441 : Blo 1156638 2609441 := bstep (se 2 (by rfl) ⟨978540, by rfl⟩ : syracuseStep 2609441 = 1957081) B1957081
theorem B1954091 : Blo 1156638 1954091 := bstep (se 1 (by rfl) ⟨1465568, by rfl⟩ : syracuseStep 1954091 = 2931137) B2931137
theorem B2937131 : Blo 1156638 2937131 := bstep (se 1 (by rfl) ⟨2202848, by rfl⟩ : syracuseStep 2937131 = 4405697) B4405697
theorem B2478521 : Blo 1156638 2478521 := bstep (se 2 (by rfl) ⟨929445, by rfl⟩ : syracuseStep 2478521 = 1858891) B1858891
theorem B2609783 : Blo 1156638 2609783 := bstep (se 1 (by rfl) ⟨1957337, by rfl⟩ : syracuseStep 2609783 = 3914675) B3914675
theorem B1954489 : Blo 1156638 1954489 := bstep (se 2 (by rfl) ⟨732933, by rfl⟩ : syracuseStep 1954489 = 1465867) B1465867
theorem B2609963 : Blo 1156638 2609963 := bstep (se 1 (by rfl) ⟨1957472, by rfl⟩ : syracuseStep 2609963 = 3914945) B3914945
theorem B1856315 : Blo 1156638 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B2675641 : Blo 1156638 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B3298315 : Blo 1156638 3298315 := bstep (se 1 (by rfl) ⟨2473736, by rfl⟩ : syracuseStep 3298315 = 4947473) B4947473
theorem B6771755 : Blo 1156638 6771755 := bstep (se 1 (by rfl) ⟨5078816, by rfl⟩ : syracuseStep 6771755 = 10157633) B10157633
theorem B2610323 : Blo 1156638 2610323 := bstep (se 1 (by rfl) ⟨1957742, by rfl⟩ : syracuseStep 2610323 = 3915485) B3915485
theorem B2610377 : Blo 1156638 2610377 := bstep (se 2 (by rfl) ⟨978891, by rfl⟩ : syracuseStep 2610377 = 1957783) B1957783
theorem B3298589 : Blo 1156638 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B1955191 : Blo 1156638 1955191 := bstep (se 1 (by rfl) ⟨1466393, by rfl⟩ : syracuseStep 1955191 = 2932787) B2932787
theorem B5952953 : Blo 1156638 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B1955387 : Blo 1156638 1955387 := bstep (se 1 (by rfl) ⟨1466540, by rfl⟩ : syracuseStep 1955387 = 2933081) B2933081
theorem B3298931 : Blo 1156638 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B2348833 : Blo 1156638 2348833 := bstep (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) B1761625
theorem B27121483 : Blo 1156638 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B19814219 : Blo 1156638 19814219 := bstep (se 1 (by rfl) ⟨14860664, by rfl⟩ : syracuseStep 19814219 = 29721329) B29721329
theorem B2971511 : Blo 1156638 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B2611079 : Blo 1156638 2611079 := bstep (se 1 (by rfl) ⟨1958309, by rfl⟩ : syracuseStep 2611079 = 3916619) B3916619
theorem B1955785 : Blo 1156638 1955785 := bstep (se 2 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 1955785 = 1466839) B1466839
theorem B8804375 : Blo 1156638 8804375 := bstep (se 1 (by rfl) ⟨6603281, by rfl⟩ : syracuseStep 8804375 = 13206563) B13206563
theorem B2611259 : Blo 1156638 2611259 := bstep (se 1 (by rfl) ⟨1958444, by rfl⟩ : syracuseStep 2611259 = 3916889) B3916889
theorem B2611385 : Blo 1156638 2611385 := bstep (se 2 (by rfl) ⟨979269, by rfl⟩ : syracuseStep 2611385 = 1958539) B1958539
theorem B5855489 : Blo 1156638 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B1235207 : Blo 1156638 1235207 := bstep (se 1 (by rfl) ⟨926405, by rfl⟩ : syracuseStep 1235207 = 1852811) B1852811
theorem B12540419 : Blo 1156638 12540419 := bstep (se 1 (by rfl) ⟨9405314, by rfl⟩ : syracuseStep 12540419 = 18810629) B18810629
theorem B3299899 : Blo 1156638 3299899 := bstep (se 1 (by rfl) ⟨2474924, by rfl⟩ : syracuseStep 3299899 = 4949849) B4949849
theorem B1956487 : Blo 1156638 1956487 := bstep (se 1 (by rfl) ⟨1467365, by rfl⟩ : syracuseStep 1956487 = 2934731) B2934731
theorem B7134155 : Blo 1156638 7134155 := bstep (se 1 (by rfl) ⟨5350616, by rfl⟩ : syracuseStep 7134155 = 10701233) B10701233
theorem B5856299 : Blo 1156638 5856299 := bstep (se 1 (by rfl) ⟨4392224, by rfl⟩ : syracuseStep 5856299 = 8784449) B8784449
theorem B1301647 : Blo 1156638 1301647 := bstep (se 1 (by rfl) ⟨976235, by rfl⟩ : syracuseStep 1301647 = 1952471) B1952471
theorem B1957135 : Blo 1156638 1957135 := bstep (se 1 (by rfl) ⟨1467851, by rfl⟩ : syracuseStep 1957135 = 2935703) B2935703
theorem B1465771 : Blo 1156638 1465771 := bstep (se 1 (by rfl) ⟨1099328, by rfl⟩ : syracuseStep 1465771 = 2198657) B2198657
theorem B1302151 : Blo 1156638 1302151 := bstep (se 1 (by rfl) ⟨976613, by rfl⟩ : syracuseStep 1302151 = 1953227) B1953227
theorem B3301049 : Blo 1156638 3301049 := bstep (se 2 (by rfl) ⟨1237893, by rfl⟩ : syracuseStep 3301049 = 2475787) B2475787
theorem B1957675 : Blo 1156638 1957675 := bstep (se 1 (by rfl) ⟨1468256, by rfl⟩ : syracuseStep 1957675 = 2936513) B2936513
theorem B1302331 : Blo 1156638 1302331 := bstep (se 1 (by rfl) ⟨976748, by rfl⟩ : syracuseStep 1302331 = 1953497) B1953497
theorem B2973593 : Blo 1156638 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B1957817 : Blo 1156638 1957817 := bstep (se 2 (by rfl) ⟨734181, by rfl⟩ : syracuseStep 1957817 = 1468363) B1468363
theorem B3301391 : Blo 1156638 3301391 := bstep (se 1 (by rfl) ⟨2476043, by rfl⟩ : syracuseStep 3301391 = 4952087) B4952087
theorem B15851543 : Blo 1156638 15851543 := bstep (se 1 (by rfl) ⟨11888657, by rfl⟩ : syracuseStep 15851543 = 23777315) B23777315
theorem B7430231 : Blo 1156638 7430231 := bstep (se 1 (by rfl) ⟨5572673, by rfl⟩ : syracuseStep 7430231 = 11145347) B11145347
theorem B2973953 : Blo 1156638 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B18800909 : Blo 1156638 18800909 := bstep (se 3 (by rfl) ⟨3525170, by rfl⟩ : syracuseStep 18800909 = 7050341) B7050341
theorem B1302799 : Blo 1156638 1302799 := bstep (se 1 (by rfl) ⟨977099, by rfl⟩ : syracuseStep 1302799 = 1954199) B1954199
theorem B5857595 : Blo 1156638 5857595 := bstep (se 1 (by rfl) ⟨4393196, by rfl⟩ : syracuseStep 5857595 = 8786393) B8786393
theorem B14836061 : Blo 1156638 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B1466743 : Blo 1156638 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B5857757 : Blo 1156638 5857757 := bstep (se 3 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 5857757 = 2196659) B2196659
theorem B1958519 : Blo 1156638 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1467067 : Blo 1156638 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B1303303 : Blo 1156638 1303303 := bstep (se 1 (by rfl) ⟨977477, by rfl⟩ : syracuseStep 1303303 = 1954955) B1954955
theorem B5858081 : Blo 1156638 5858081 := bstep (se 2 (by rfl) ⟨2196780, by rfl⟩ : syracuseStep 5858081 = 4393561) B4393561
theorem B3302279 : Blo 1156638 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B1303483 : Blo 1156638 1303483 := bstep (se 1 (by rfl) ⟨977612, by rfl⟩ : syracuseStep 1303483 = 1955225) B1955225
theorem B3302461 : Blo 1156638 3302461 := bstep (se 3 (by rfl) ⟨619211, by rfl⟩ : syracuseStep 3302461 = 1238423) B1238423
theorem B3302689 : Blo 1156638 3302689 := bstep (se 2 (by rfl) ⟨1238508, by rfl⟩ : syracuseStep 3302689 = 2477017) B2477017
theorem B1303951 : Blo 1156638 1303951 := bstep (se 1 (by rfl) ⟨977963, by rfl⟩ : syracuseStep 1303951 = 1955927) B1955927
theorem B7923091 : Blo 1156638 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B25748941 : Blo 1156638 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B4941323 : Blo 1156638 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B16934429 : Blo 1156638 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B3303031 : Blo 1156638 3303031 := bstep (se 1 (by rfl) ⟨2477273, by rfl⟩ : syracuseStep 3303031 = 4954547) B4954547
theorem B1468039 : Blo 1156638 1468039 := bstep (se 1 (by rfl) ⟨1101029, by rfl⟩ : syracuseStep 1468039 = 2202059) B2202059
theorem B5859053 : Blo 1156638 5859053 := bstep (se 3 (by rfl) ⟨1098572, by rfl⟩ : syracuseStep 5859053 = 2197145) B2197145
theorem B5793569 : Blo 1156638 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B1304455 : Blo 1156638 1304455 := bstep (se 1 (by rfl) ⟨978341, by rfl⟩ : syracuseStep 1304455 = 1956683) B1956683
theorem B1468459 : Blo 1156638 1468459 := bstep (se 1 (by rfl) ⟨1101344, by rfl⟩ : syracuseStep 1468459 = 2202689) B2202689
theorem B1304635 : Blo 1156638 1304635 := bstep (se 1 (by rfl) ⟨978476, by rfl⟩ : syracuseStep 1304635 = 1956953) B1956953
theorem B1239175 : Blo 1156638 1239175 := bstep (se 1 (by rfl) ⟨929381, by rfl⟩ : syracuseStep 1239175 = 1858763) B1858763
theorem B2975891 : Blo 1156638 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B1468687 : Blo 1156638 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B1305103 : Blo 1156638 1305103 := bstep (se 1 (by rfl) ⟨978827, by rfl⟩ : syracuseStep 1305103 = 1957655) B1957655
theorem B5859863 : Blo 1156638 5859863 := bstep (se 1 (by rfl) ⟨4394897, by rfl⟩ : syracuseStep 5859863 = 8789795) B8789795
theorem B3303965 : Blo 1156638 3303965 := bstep (se 3 (by rfl) ⟨619493, by rfl⟩ : syracuseStep 3303965 = 1238987) B1238987
theorem B3304307 : Blo 1156638 3304307 := bstep (se 1 (by rfl) ⟨2478230, by rfl⟩ : syracuseStep 3304307 = 4956461) B4956461
theorem B1305607 : Blo 1156638 1305607 := bstep (se 1 (by rfl) ⟨979205, by rfl⟩ : syracuseStep 1305607 = 1958411) B1958411
theorem B12545225 : Blo 1156638 12545225 := bstep (se 2 (by rfl) ⟨4704459, by rfl⟩ : syracuseStep 12545225 = 9408919) B9408919
theorem B3304763 : Blo 1156638 3304763 := bstep (se 1 (by rfl) ⟨2478572, by rfl⟩ : syracuseStep 3304763 = 4957145) B4957145
theorem B1568201 : Blo 1156638 1568201 := bstep (se 2 (by rfl) ⟨588075, by rfl⟩ : syracuseStep 1568201 = 1176151) B1176151
theorem B22244867 : Blo 1156638 22244867 := bstep (se 1 (by rfl) ⟨16683650, by rfl⟩ : syracuseStep 22244867 = 33367301) B33367301
theorem B7433795 : Blo 1156638 7433795 := bstep (se 1 (by rfl) ⟨5575346, by rfl⟩ : syracuseStep 7433795 = 11150693) B11150693
theorem B21131009 : Blo 1156638 21131009 := bstep (se 2 (by rfl) ⟨7924128, by rfl⟩ : syracuseStep 21131009 = 15848257) B15848257
theorem B5566583 : Blo 1156638 5566583 := bstep (se 1 (by rfl) ⟨4174937, by rfl⟩ : syracuseStep 5566583 = 8349875) B8349875
theorem B5566735 : Blo 1156638 5566735 := bstep (se 1 (by rfl) ⟨4175051, by rfl⟩ : syracuseStep 5566735 = 8350103) B8350103
theorem B4452893 : Blo 1156638 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B12546737 : Blo 1156638 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B15070067 : Blo 1156638 15070067 := bstep (se 1 (by rfl) ⟨11302550, by rfl⟩ : syracuseStep 15070067 = 22605101) B22605101
theorem B3339379 : Blo 1156638 3339379 := bstep (se 1 (by rfl) ⟨2504534, by rfl⟩ : syracuseStep 3339379 = 5009069) B5009069
theorem B90273005 : Blo 1156638 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B2782475 : Blo 1156638 2782475 := bstep (se 1 (by rfl) ⟨2086856, by rfl⟩ : syracuseStep 2782475 = 4173713) B4173713
theorem B5862941 : Blo 1156638 5862941 := bstep (se 3 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 5862941 = 2198603) B2198603
theorem B5568061 : Blo 1156638 5568061 := bstep (se 3 (by rfl) ⟨1044011, by rfl⟩ : syracuseStep 5568061 = 2088023) B2088023
theorem B4945475 : Blo 1156638 4945475 := bstep (se 1 (by rfl) ⟨3709106, by rfl⟩ : syracuseStep 4945475 = 7418213) B7418213
theorem B8812151 : Blo 1156638 8812151 := bstep (se 1 (by rfl) ⟨6609113, by rfl⟩ : syracuseStep 8812151 = 13218227) B13218227
theorem B4945697 : Blo 1156638 4945697 := bstep (se 2 (by rfl) ⟨1854636, by rfl⟩ : syracuseStep 4945697 = 3709273) B3709273
theorem B4454279 : Blo 1156638 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B4945799 : Blo 1156638 4945799 := bstep (se 1 (by rfl) ⟨3709349, by rfl⟩ : syracuseStep 4945799 = 7418699) B7418699
theorem B5863427 : Blo 1156638 5863427 := bstep (se 1 (by rfl) ⟨4397570, by rfl⟩ : syracuseStep 5863427 = 8795141) B8795141
theorem B2783243 : Blo 1156638 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B3176567 : Blo 1156638 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B1734971 : Blo 1156638 1734971 := bstep (se 1 (by rfl) ⟨1301228, by rfl⟩ : syracuseStep 1734971 = 2602457) B2602457
theorem B1735031 : Blo 1156638 1735031 := bstep (se 1 (by rfl) ⟨1301273, by rfl⟩ : syracuseStep 1735031 = 2602547) B2602547
theorem B1669511 : Blo 1156638 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B1735055 : Blo 1156638 1735055 := bstep (se 1 (by rfl) ⟨1301291, by rfl⟩ : syracuseStep 1735055 = 2602583) B2602583
theorem B73202069 : Blo 1156638 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B1735097 : Blo 1156638 1735097 := bstep (se 2 (by rfl) ⟨650661, by rfl⟩ : syracuseStep 1735097 = 1301323) B1301323
theorem B1735175 : Blo 1156638 1735175 := bstep (se 1 (by rfl) ⟨1301381, by rfl⟩ : syracuseStep 1735175 = 2602763) B2602763
theorem B1735211 : Blo 1156638 1735211 := bstep (se 1 (by rfl) ⟨1301408, by rfl⟩ : syracuseStep 1735211 = 2602817) B2602817
theorem B8813123 : Blo 1156638 8813123 := bstep (se 1 (by rfl) ⟨6609842, by rfl⟩ : syracuseStep 8813123 = 13219685) B13219685
theorem B1735241 : Blo 1156638 1735241 := bstep (se 2 (by rfl) ⟨650715, by rfl⟩ : syracuseStep 1735241 = 1301431) B1301431
theorem B23788151 : Blo 1156638 23788151 := bstep (se 1 (by rfl) ⟨17841113, by rfl⟩ : syracuseStep 23788151 = 35682227) B35682227
theorem B1735355 : Blo 1156638 1735355 := bstep (se 1 (by rfl) ⟨1301516, by rfl⟩ : syracuseStep 1735355 = 2603033) B2603033
theorem B1735415 : Blo 1156638 1735415 := bstep (se 1 (by rfl) ⟨1301561, by rfl⟩ : syracuseStep 1735415 = 2603123) B2603123
theorem B1735439 : Blo 1156638 1735439 := bstep (se 1 (by rfl) ⟨1301579, by rfl⟩ : syracuseStep 1735439 = 2603159) B2603159
theorem B1735481 : Blo 1156638 1735481 := bstep (se 2 (by rfl) ⟨650805, by rfl⟩ : syracuseStep 1735481 = 1301611) B1301611
theorem B3963763 : Blo 1156638 3963763 := bstep (se 1 (by rfl) ⟨2972822, by rfl⟩ : syracuseStep 3963763 = 5945645) B5945645
theorem B1735559 : Blo 1156638 1735559 := bstep (se 1 (by rfl) ⟨1301669, by rfl⟩ : syracuseStep 1735559 = 2603339) B2603339
theorem B1735595 : Blo 1156638 1735595 := bstep (se 1 (by rfl) ⟨1301696, by rfl⟩ : syracuseStep 1735595 = 2603393) B2603393
theorem B2784185 : Blo 1156638 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B1735625 : Blo 1156638 1735625 := bstep (se 2 (by rfl) ⟨650859, by rfl⟩ : syracuseStep 1735625 = 1301719) B1301719
theorem B2784299 : Blo 1156638 2784299 := bstep (se 1 (by rfl) ⟨2088224, by rfl⟩ : syracuseStep 2784299 = 4176449) B4176449
theorem B1735739 : Blo 1156638 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B1735799 : Blo 1156638 1735799 := bstep (se 1 (by rfl) ⟨1301849, by rfl⟩ : syracuseStep 1735799 = 2603699) B2603699
theorem B1735823 : Blo 1156638 1735823 := bstep (se 1 (by rfl) ⟨1301867, by rfl⟩ : syracuseStep 1735823 = 2603735) B2603735
theorem B1735865 : Blo 1156638 1735865 := bstep (se 2 (by rfl) ⟨650949, by rfl⟩ : syracuseStep 1735865 = 1301899) B1301899
theorem B1735943 : Blo 1156638 1735943 := bstep (se 1 (by rfl) ⟨1301957, by rfl⟩ : syracuseStep 1735943 = 2603915) B2603915
theorem B1735979 : Blo 1156638 1735979 := bstep (se 1 (by rfl) ⟨1301984, by rfl⟩ : syracuseStep 1735979 = 2603969) B2603969
theorem B1736009 : Blo 1156638 1736009 := bstep (se 2 (by rfl) ⟨651003, by rfl⟩ : syracuseStep 1736009 = 1302007) B1302007
theorem B1736123 : Blo 1156638 1736123 := bstep (se 1 (by rfl) ⟨1302092, by rfl⟩ : syracuseStep 1736123 = 2604185) B2604185
theorem B1736183 : Blo 1156638 1736183 := bstep (se 1 (by rfl) ⟨1302137, by rfl⟩ : syracuseStep 1736183 = 2604275) B2604275
theorem B1736207 : Blo 1156638 1736207 := bstep (se 1 (by rfl) ⟨1302155, by rfl⟩ : syracuseStep 1736207 = 2604311) B2604311
theorem B1736249 : Blo 1156638 1736249 := bstep (se 2 (by rfl) ⟨651093, by rfl⟩ : syracuseStep 1736249 = 1302187) B1302187
theorem B5865047 : Blo 1156638 5865047 := bstep (se 1 (by rfl) ⟨4398785, by rfl⟩ : syracuseStep 5865047 = 8797571) B8797571
theorem B114392675 : Blo 1156638 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B1736327 : Blo 1156638 1736327 := bstep (se 1 (by rfl) ⟨1302245, by rfl⟩ : syracuseStep 1736327 = 2604491) B2604491
theorem B1736363 : Blo 1156638 1736363 := bstep (se 1 (by rfl) ⟨1302272, by rfl⟩ : syracuseStep 1736363 = 2604545) B2604545
theorem B1736393 : Blo 1156638 1736393 := bstep (se 2 (by rfl) ⟨651147, by rfl⟩ : syracuseStep 1736393 = 1302295) B1302295
theorem B4947713 : Blo 1156638 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B1736507 : Blo 1156638 1736507 := bstep (se 1 (by rfl) ⟨1302380, by rfl⟩ : syracuseStep 1736507 = 2604761) B2604761
theorem B1736567 : Blo 1156638 1736567 := bstep (se 1 (by rfl) ⟨1302425, by rfl⟩ : syracuseStep 1736567 = 2604851) B2604851
theorem B1736591 : Blo 1156638 1736591 := bstep (se 1 (by rfl) ⟨1302443, by rfl⟩ : syracuseStep 1736591 = 2604887) B2604887
theorem B1736633 : Blo 1156638 1736633 := bstep (se 2 (by rfl) ⟨651237, by rfl⟩ : syracuseStep 1736633 = 1302475) B1302475
theorem B42270781 : Blo 1156638 42270781 := bstep (se 3 (by rfl) ⟨7925771, by rfl⟩ : syracuseStep 42270781 = 15851543) B15851543
theorem B1736783 : Blo 1156638 1736783 := bstep (se 1 (by rfl) ⟨1302587, by rfl⟩ : syracuseStep 1736783 = 2605175) B2605175
theorem B1736903 : Blo 1156638 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B1737065 : Blo 1156638 1737065 := bstep (se 2 (by rfl) ⟨651399, by rfl⟩ : syracuseStep 1737065 = 1302799) B1302799
theorem B5865857 : Blo 1156638 5865857 := bstep (se 2 (by rfl) ⟨2199696, by rfl⟩ : syracuseStep 5865857 = 4399393) B4399393
theorem B1737143 : Blo 1156638 1737143 := bstep (se 1 (by rfl) ⟨1302857, by rfl⟩ : syracuseStep 1737143 = 2605715) B2605715
theorem B1737179 : Blo 1156638 1737179 := bstep (se 1 (by rfl) ⟨1302884, by rfl⟩ : syracuseStep 1737179 = 2605769) B2605769
theorem B11141657 : Blo 1156638 11141657 := bstep (se 2 (by rfl) ⟨4178121, by rfl⟩ : syracuseStep 11141657 = 8356243) B8356243
theorem B7930541 : Blo 1156638 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B1737647 : Blo 1156638 1737647 := bstep (se 1 (by rfl) ⟨1303235, by rfl⟩ : syracuseStep 1737647 = 2606471) B2606471
theorem B6259639 : Blo 1156638 6259639 := bstep (se 1 (by rfl) ⟨4694729, by rfl⟩ : syracuseStep 6259639 = 9389459) B9389459
theorem B1737737 : Blo 1156638 1737737 := bstep (se 2 (by rfl) ⟨651651, by rfl⟩ : syracuseStep 1737737 = 1303303) B1303303
theorem B1737767 : Blo 1156638 1737767 := bstep (se 1 (by rfl) ⟨1303325, by rfl⟩ : syracuseStep 1737767 = 2606651) B2606651
theorem B1737851 : Blo 1156638 1737851 := bstep (se 1 (by rfl) ⟨1303388, by rfl⟩ : syracuseStep 1737851 = 2606777) B2606777
theorem B4392089 : Blo 1156638 4392089 := bstep (se 2 (by rfl) ⟨1647033, by rfl⟩ : syracuseStep 4392089 = 3294067) B3294067
theorem B5866667 : Blo 1156638 5866667 := bstep (se 1 (by rfl) ⟨4400000, by rfl⟩ : syracuseStep 5866667 = 8800001) B8800001
theorem B1737977 : Blo 1156638 1737977 := bstep (se 2 (by rfl) ⟨651741, by rfl⟩ : syracuseStep 1737977 = 1303483) B1303483
theorem B1738079 : Blo 1156638 1738079 := bstep (se 1 (by rfl) ⟨1303559, by rfl⟩ : syracuseStep 1738079 = 2607119) B2607119
theorem B1738091 : Blo 1156638 1738091 := bstep (se 1 (by rfl) ⟨1303568, by rfl⟩ : syracuseStep 1738091 = 2607137) B2607137
theorem B1738319 : Blo 1156638 1738319 := bstep (se 1 (by rfl) ⟨1303739, by rfl⟩ : syracuseStep 1738319 = 2607479) B2607479
theorem B2197115 : Blo 1156638 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B9406091 : Blo 1156638 9406091 := bstep (se 1 (by rfl) ⟨7054568, by rfl⟩ : syracuseStep 9406091 = 14109137) B14109137
theorem B5867153 : Blo 1156638 5867153 := bstep (se 2 (by rfl) ⟨2200182, by rfl⟩ : syracuseStep 5867153 = 4400365) B4400365
theorem B1738439 : Blo 1156638 1738439 := bstep (se 1 (by rfl) ⟨1303829, by rfl⟩ : syracuseStep 1738439 = 2607659) B2607659
theorem B2197343 : Blo 1156638 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B11143007 : Blo 1156638 11143007 := bstep (se 1 (by rfl) ⟨8357255, by rfl⟩ : syracuseStep 11143007 = 16714511) B16714511
theorem B1738601 : Blo 1156638 1738601 := bstep (se 2 (by rfl) ⟨651975, by rfl⟩ : syracuseStep 1738601 = 1303951) B1303951
theorem B1738679 : Blo 1156638 1738679 := bstep (se 1 (by rfl) ⟨1304009, by rfl⟩ : syracuseStep 1738679 = 2608019) B2608019
theorem B1738715 : Blo 1156638 1738715 := bstep (se 1 (by rfl) ⟨1304036, by rfl⟩ : syracuseStep 1738715 = 2608073) B2608073
theorem B33458183 : Blo 1156638 33458183 := bstep (se 1 (by rfl) ⟨25093637, by rfl⟩ : syracuseStep 33458183 = 50187275) B50187275
theorem B2197601 : Blo 1156638 2197601 := bstep (se 2 (by rfl) ⟨824100, by rfl⟩ : syracuseStep 2197601 = 1648201) B1648201
theorem B4393075 : Blo 1156638 4393075 := bstep (se 1 (by rfl) ⟨3294806, by rfl⟩ : syracuseStep 4393075 = 6589613) B6589613
theorem B4950173 : Blo 1156638 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B2197867 : Blo 1156638 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B1739183 : Blo 1156638 1739183 := bstep (se 1 (by rfl) ⟨1304387, by rfl⟩ : syracuseStep 1739183 = 2608775) B2608775
theorem B1739273 : Blo 1156638 1739273 := bstep (se 2 (by rfl) ⟨652227, by rfl⟩ : syracuseStep 1739273 = 1304455) B1304455
theorem B1739303 : Blo 1156638 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B1739387 : Blo 1156638 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B1739513 : Blo 1156638 1739513 := bstep (se 2 (by rfl) ⟨652317, by rfl⟩ : syracuseStep 1739513 = 1304635) B1304635
theorem B1739615 : Blo 1156638 1739615 := bstep (se 1 (by rfl) ⟨1304711, by rfl⟩ : syracuseStep 1739615 = 2609423) B2609423
theorem B4393835 : Blo 1156638 4393835 := bstep (se 1 (by rfl) ⟨3295376, by rfl⟩ : syracuseStep 4393835 = 6590753) B6590753
theorem B1739627 : Blo 1156638 1739627 := bstep (se 1 (by rfl) ⟨1304720, by rfl⟩ : syracuseStep 1739627 = 2609441) B2609441
theorem B1739855 : Blo 1156638 1739855 := bstep (se 1 (by rfl) ⟨1304891, by rfl⟩ : syracuseStep 1739855 = 2609783) B2609783
theorem B1739975 : Blo 1156638 1739975 := bstep (se 1 (by rfl) ⟨1304981, by rfl⟩ : syracuseStep 1739975 = 2609963) B2609963
theorem B128519459 : Blo 1156638 128519459 := bstep (se 1 (by rfl) ⟨96389594, by rfl⟩ : syracuseStep 128519459 = 192779189) B192779189
theorem B1740137 : Blo 1156638 1740137 := bstep (se 2 (by rfl) ⟨652551, by rfl⟩ : syracuseStep 1740137 = 1305103) B1305103
theorem B1740215 : Blo 1156638 1740215 := bstep (se 1 (by rfl) ⟨1305161, by rfl⟩ : syracuseStep 1740215 = 2610323) B2610323
theorem B1740251 : Blo 1156638 1740251 := bstep (se 1 (by rfl) ⟨1305188, by rfl⟩ : syracuseStep 1740251 = 2610377) B2610377
theorem B2199059 : Blo 1156638 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B3968635 : Blo 1156638 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B2199287 : Blo 1156638 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B5869421 : Blo 1156638 5869421 := bstep (se 3 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 5869421 = 2201033) B2201033
theorem B13209479 : Blo 1156638 13209479 := bstep (se 1 (by rfl) ⟨9907109, by rfl⟩ : syracuseStep 13209479 = 19814219) B19814219
theorem B1740719 : Blo 1156638 1740719 := bstep (se 1 (by rfl) ⟨1305539, by rfl⟩ : syracuseStep 1740719 = 2611079) B2611079
theorem B1740809 : Blo 1156638 1740809 := bstep (se 2 (by rfl) ⟨652803, by rfl⟩ : syracuseStep 1740809 = 1305607) B1305607
theorem B56299531 : Blo 1156638 56299531 := bstep (se 1 (by rfl) ⟨42224648, by rfl⟩ : syracuseStep 56299531 = 84449297) B84449297
theorem B5869583 : Blo 1156638 5869583 := bstep (se 1 (by rfl) ⟨4402187, by rfl⟩ : syracuseStep 5869583 = 8804375) B8804375
theorem B1740839 : Blo 1156638 1740839 := bstep (se 1 (by rfl) ⟨1305629, by rfl⟩ : syracuseStep 1740839 = 2611259) B2611259
theorem B1740923 : Blo 1156638 1740923 := bstep (se 1 (by rfl) ⟨1305692, by rfl⟩ : syracuseStep 1740923 = 2611385) B2611385
theorem B3969181 : Blo 1156638 3969181 := bstep (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) B1488443
theorem B3903659 : Blo 1156638 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B17174705 : Blo 1156638 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B8360279 : Blo 1156638 8360279 := bstep (se 1 (by rfl) ⟨6270209, by rfl⟩ : syracuseStep 8360279 = 12540419) B12540419
theorem B13177403 : Blo 1156638 13177403 := bstep (se 1 (by rfl) ⟨9883052, by rfl⟩ : syracuseStep 13177403 = 19766105) B19766105
theorem B4756103 : Blo 1156638 4756103 := bstep (se 1 (by rfl) ⟨3567077, by rfl⟩ : syracuseStep 4756103 = 7134155) B7134155
theorem B3904199 : Blo 1156638 3904199 := bstep (se 1 (by rfl) ⟨2928149, by rfl⟩ : syracuseStep 3904199 = 5856299) B5856299
theorem B4756333 : Blo 1156638 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B2200699 : Blo 1156638 2200699 := bstep (se 1 (by rfl) ⟨1650524, by rfl⟩ : syracuseStep 2200699 = 3301049) B3301049
theorem B7410959 : Blo 1156638 7410959 := bstep (se 1 (by rfl) ⟨5558219, by rfl⟩ : syracuseStep 7410959 = 11116439) B11116439
theorem B17831261 : Blo 1156638 17831261 := bstep (se 3 (by rfl) ⟨3343361, by rfl⟩ : syracuseStep 17831261 = 6686723) B6686723
theorem B2200927 : Blo 1156638 2200927 := bstep (se 1 (by rfl) ⟨1650695, by rfl⟩ : syracuseStep 2200927 = 3301391) B3301391
theorem B4953487 : Blo 1156638 4953487 := bstep (se 1 (by rfl) ⟨3715115, by rfl⟩ : syracuseStep 4953487 = 7430231) B7430231
theorem B8787365 : Blo 1156638 8787365 := bstep (se 4 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 8787365 = 1647631) B1647631
theorem B3905063 : Blo 1156638 3905063 := bstep (se 1 (by rfl) ⟨2928797, by rfl⟩ : syracuseStep 3905063 = 5857595) B5857595
theorem B2201185 : Blo 1156638 2201185 := bstep (se 2 (by rfl) ⟨825444, by rfl⟩ : syracuseStep 2201185 = 1650889) B1650889
theorem B3905171 : Blo 1156638 3905171 := bstep (se 1 (by rfl) ⟨2928878, by rfl⟩ : syracuseStep 3905171 = 5857757) B5857757
theorem B12523207 : Blo 1156638 12523207 := bstep (se 1 (by rfl) ⟨9392405, by rfl⟩ : syracuseStep 12523207 = 18784811) B18784811
theorem B8361721 : Blo 1156638 8361721 := bstep (se 2 (by rfl) ⟨3135645, by rfl⟩ : syracuseStep 8361721 = 6271291) B6271291
theorem B3905387 : Blo 1156638 3905387 := bstep (se 1 (by rfl) ⟨2929040, by rfl⟩ : syracuseStep 3905387 = 5858081) B5858081
theorem B3905441 : Blo 1156638 3905441 := bstep (se 2 (by rfl) ⟨1464540, by rfl⟩ : syracuseStep 3905441 = 2929081) B2929081
theorem B2201519 : Blo 1156638 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B144644237 : Blo 1156638 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B3906035 : Blo 1156638 3906035 := bstep (se 1 (by rfl) ⟨2929526, by rfl⟩ : syracuseStep 3906035 = 5859053) B5859053
theorem B4397753 : Blo 1156638 4397753 := bstep (se 2 (by rfl) ⟨1649157, by rfl⟩ : syracuseStep 4397753 = 3298315) B3298315
theorem B5872337 : Blo 1156638 5872337 := bstep (se 2 (by rfl) ⟨2202126, by rfl⟩ : syracuseStep 5872337 = 4404253) B4404253
theorem B3906575 : Blo 1156638 3906575 := bstep (se 1 (by rfl) ⟨2929931, by rfl⟩ : syracuseStep 3906575 = 5859863) B5859863
theorem B2202643 : Blo 1156638 2202643 := bstep (se 1 (by rfl) ⟨1651982, by rfl⟩ : syracuseStep 2202643 = 3303965) B3303965
theorem B2202871 : Blo 1156638 2202871 := bstep (se 1 (by rfl) ⟨1652153, by rfl⟩ : syracuseStep 2202871 = 3304307) B3304307
theorem B8363483 : Blo 1156638 8363483 := bstep (se 1 (by rfl) ⟨6272612, by rfl⟩ : syracuseStep 8363483 = 12545225) B12545225
theorem B2203175 : Blo 1156638 2203175 := bstep (se 1 (by rfl) ⟨1652381, by rfl⟩ : syracuseStep 2203175 = 3304763) B3304763
theorem B3907169 : Blo 1156638 3907169 := bstep (se 2 (by rfl) ⟨1465188, by rfl⟩ : syracuseStep 3907169 = 2930377) B2930377
theorem B4955863 : Blo 1156638 4955863 := bstep (se 1 (by rfl) ⟨3716897, by rfl⟩ : syracuseStep 4955863 = 7433795) B7433795
theorem B4464503 : Blo 1156638 4464503 := bstep (se 1 (by rfl) ⟨3348377, by rfl⟩ : syracuseStep 4464503 = 6696755) B6696755
theorem B8363969 : Blo 1156638 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B3711055 : Blo 1156638 3711055 := bstep (se 1 (by rfl) ⟨2783291, by rfl⟩ : syracuseStep 3711055 = 5566583) B5566583
theorem B32579941 : Blo 1156638 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B8364491 : Blo 1156638 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B4399865 : Blo 1156638 4399865 := bstep (se 2 (by rfl) ⟨1649949, by rfl⟩ : syracuseStep 4399865 = 3299899) B3299899
theorem B1647535 : Blo 1156638 1647535 := bstep (se 1 (by rfl) ⟨1235651, by rfl⟩ : syracuseStep 1647535 = 2471303) B2471303
theorem B3908627 : Blo 1156638 3908627 := bstep (se 1 (by rfl) ⟨2931470, by rfl⟩ : syracuseStep 3908627 = 5862941) B5862941
theorem B5874767 : Blo 1156638 5874767 := bstep (se 1 (by rfl) ⟨4406075, by rfl⟩ : syracuseStep 5874767 = 8812151) B8812151
theorem B5285017 : Blo 1156638 5285017 := bstep (se 2 (by rfl) ⟨1981881, by rfl⟩ : syracuseStep 5285017 = 3963763) B3963763
theorem B3908951 : Blo 1156638 3908951 := bstep (se 1 (by rfl) ⟨2931713, by rfl⟩ : syracuseStep 3908951 = 5863427) B5863427
theorem B7153039 : Blo 1156638 7153039 := bstep (se 1 (by rfl) ⟨5364779, by rfl⟩ : syracuseStep 7153039 = 10729559) B10729559
theorem B1156647 : Blo 1156638 1156647 := bstep (se 1 (by rfl) ⟨867485, by rfl⟩ : syracuseStep 1156647 = 1734971) B1734971
theorem B1156687 : Blo 1156638 1156687 := bstep (se 1 (by rfl) ⟨867515, by rfl⟩ : syracuseStep 1156687 = 1735031) B1735031
theorem B1156703 : Blo 1156638 1156703 := bstep (se 1 (by rfl) ⟨867527, by rfl⟩ : syracuseStep 1156703 = 1735055) B1735055
theorem B48801379 : Blo 1156638 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B1156731 : Blo 1156638 1156731 := bstep (se 1 (by rfl) ⟨867548, by rfl⟩ : syracuseStep 1156731 = 1735097) B1735097
theorem B1156783 : Blo 1156638 1156783 := bstep (se 1 (by rfl) ⟨867587, by rfl⟩ : syracuseStep 1156783 = 1735175) B1735175
theorem B1156807 : Blo 1156638 1156807 := bstep (se 1 (by rfl) ⟨867605, by rfl⟩ : syracuseStep 1156807 = 1735211) B1735211
theorem B4400851 : Blo 1156638 4400851 := bstep (se 1 (by rfl) ⟨3300638, by rfl⟩ : syracuseStep 4400851 = 6601277) B6601277
theorem B5875415 : Blo 1156638 5875415 := bstep (se 1 (by rfl) ⟨4406561, by rfl⟩ : syracuseStep 5875415 = 8813123) B8813123
theorem B1156827 : Blo 1156638 1156827 := bstep (se 1 (by rfl) ⟨867620, by rfl⟩ : syracuseStep 1156827 = 1735241) B1735241
theorem B1156903 : Blo 1156638 1156903 := bstep (se 1 (by rfl) ⟨867677, by rfl⟩ : syracuseStep 1156903 = 1735355) B1735355
theorem B1156943 : Blo 1156638 1156943 := bstep (se 1 (by rfl) ⟨867707, by rfl⟩ : syracuseStep 1156943 = 1735415) B1735415
theorem B1156959 : Blo 1156638 1156959 := bstep (se 1 (by rfl) ⟨867719, by rfl⟩ : syracuseStep 1156959 = 1735439) B1735439
theorem B1156987 : Blo 1156638 1156987 := bstep (se 1 (by rfl) ⟨867740, by rfl⟩ : syracuseStep 1156987 = 1735481) B1735481
theorem B1157039 : Blo 1156638 1157039 := bstep (se 1 (by rfl) ⟨867779, by rfl⟩ : syracuseStep 1157039 = 1735559) B1735559
theorem B1157063 : Blo 1156638 1157063 := bstep (se 1 (by rfl) ⟨867797, by rfl⟩ : syracuseStep 1157063 = 1735595) B1735595
theorem B1157083 : Blo 1156638 1157083 := bstep (se 1 (by rfl) ⟨867812, by rfl⟩ : syracuseStep 1157083 = 1735625) B1735625
theorem B1157159 : Blo 1156638 1157159 := bstep (se 1 (by rfl) ⟨867869, by rfl⟩ : syracuseStep 1157159 = 1735739) B1735739
theorem B1648679 : Blo 1156638 1648679 := bstep (se 1 (by rfl) ⟨1236509, by rfl⟩ : syracuseStep 1648679 = 2473019) B2473019
theorem B1157199 : Blo 1156638 1157199 := bstep (se 1 (by rfl) ⟨867899, by rfl⟩ : syracuseStep 1157199 = 1735799) B1735799
theorem B1157215 : Blo 1156638 1157215 := bstep (se 1 (by rfl) ⟨867911, by rfl⟩ : syracuseStep 1157215 = 1735823) B1735823
theorem B1157243 : Blo 1156638 1157243 := bstep (se 1 (by rfl) ⟨867932, by rfl⟩ : syracuseStep 1157243 = 1735865) B1735865
theorem B4401323 : Blo 1156638 4401323 := bstep (se 1 (by rfl) ⟨3300992, by rfl⟩ : syracuseStep 4401323 = 6601985) B6601985
theorem B1157295 : Blo 1156638 1157295 := bstep (se 1 (by rfl) ⟨867971, by rfl⟩ : syracuseStep 1157295 = 1735943) B1735943
theorem B1157319 : Blo 1156638 1157319 := bstep (se 1 (by rfl) ⟨867989, by rfl⟩ : syracuseStep 1157319 = 1735979) B1735979
theorem B1157339 : Blo 1156638 1157339 := bstep (se 1 (by rfl) ⟨868004, by rfl⟩ : syracuseStep 1157339 = 1736009) B1736009
theorem B1157415 : Blo 1156638 1157415 := bstep (se 1 (by rfl) ⟨868061, by rfl⟩ : syracuseStep 1157415 = 1736123) B1736123
theorem B1157455 : Blo 1156638 1157455 := bstep (se 1 (by rfl) ⟨868091, by rfl⟩ : syracuseStep 1157455 = 1736183) B1736183
theorem B1157471 : Blo 1156638 1157471 := bstep (se 1 (by rfl) ⟨868103, by rfl⟩ : syracuseStep 1157471 = 1736207) B1736207
theorem B1157499 : Blo 1156638 1157499 := bstep (se 1 (by rfl) ⟨868124, by rfl⟩ : syracuseStep 1157499 = 1736249) B1736249
theorem B3910031 : Blo 1156638 3910031 := bstep (se 1 (by rfl) ⟨2932523, by rfl⟩ : syracuseStep 3910031 = 5865047) B5865047
theorem B76261783 : Blo 1156638 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B1157551 : Blo 1156638 1157551 := bstep (se 1 (by rfl) ⟨868163, by rfl⟩ : syracuseStep 1157551 = 1736327) B1736327
theorem B1157575 : Blo 1156638 1157575 := bstep (se 1 (by rfl) ⟨868181, by rfl⟩ : syracuseStep 1157575 = 1736363) B1736363
theorem B1157595 : Blo 1156638 1157595 := bstep (se 1 (by rfl) ⟨868196, by rfl⟩ : syracuseStep 1157595 = 1736393) B1736393
theorem B1157671 : Blo 1156638 1157671 := bstep (se 1 (by rfl) ⟨868253, by rfl⟩ : syracuseStep 1157671 = 1736507) B1736507
theorem B19016237 : Blo 1156638 19016237 := bstep (se 3 (by rfl) ⟨3565544, by rfl⟩ : syracuseStep 19016237 = 7131089) B7131089
theorem B1157711 : Blo 1156638 1157711 := bstep (se 1 (by rfl) ⟨868283, by rfl⟩ : syracuseStep 1157711 = 1736567) B1736567
theorem B1157727 : Blo 1156638 1157727 := bstep (se 1 (by rfl) ⟨868295, by rfl⟩ : syracuseStep 1157727 = 1736591) B1736591
theorem B1157755 : Blo 1156638 1157755 := bstep (se 1 (by rfl) ⟨868316, by rfl⟩ : syracuseStep 1157755 = 1736633) B1736633
theorem B8792711 : Blo 1156638 8792711 := bstep (se 1 (by rfl) ⟨6594533, by rfl⟩ : syracuseStep 8792711 = 13189067) B13189067
theorem B1157807 : Blo 1156638 1157807 := bstep (se 1 (by rfl) ⟨868355, by rfl⟩ : syracuseStep 1157807 = 1736711) B1736711
theorem B1157831 : Blo 1156638 1157831 := bstep (se 1 (by rfl) ⟨868373, by rfl⟩ : syracuseStep 1157831 = 1736747) B1736747
theorem B3910355 : Blo 1156638 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B1157851 : Blo 1156638 1157851 := bstep (se 1 (by rfl) ⟨868388, by rfl⟩ : syracuseStep 1157851 = 1736777) B1736777
theorem B1157927 : Blo 1156638 1157927 := bstep (se 1 (by rfl) ⟨868445, by rfl⟩ : syracuseStep 1157927 = 1736891) B1736891
theorem B1157967 : Blo 1156638 1157967 := bstep (se 1 (by rfl) ⟨868475, by rfl⟩ : syracuseStep 1157967 = 1736951) B1736951
theorem B1157983 : Blo 1156638 1157983 := bstep (se 1 (by rfl) ⟨868487, by rfl⟩ : syracuseStep 1157983 = 1736975) B1736975
theorem B1158011 : Blo 1156638 1158011 := bstep (se 1 (by rfl) ⟨868508, by rfl⟩ : syracuseStep 1158011 = 1737017) B1737017
theorem B1158063 : Blo 1156638 1158063 := bstep (se 1 (by rfl) ⟨868547, by rfl⟩ : syracuseStep 1158063 = 1737095) B1737095
theorem B1158087 : Blo 1156638 1158087 := bstep (se 1 (by rfl) ⟨868565, by rfl⟩ : syracuseStep 1158087 = 1737131) B1737131
theorem B1158107 : Blo 1156638 1158107 := bstep (se 1 (by rfl) ⟨868580, by rfl⟩ : syracuseStep 1158107 = 1737161) B1737161
theorem B4074515 : Blo 1156638 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B1158183 : Blo 1156638 1158183 := bstep (se 1 (by rfl) ⟨868637, by rfl⟩ : syracuseStep 1158183 = 1737275) B1737275
theorem B1158223 : Blo 1156638 1158223 := bstep (se 1 (by rfl) ⟨868667, by rfl⟩ : syracuseStep 1158223 = 1737335) B1737335
theorem B1158239 : Blo 1156638 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B1158267 : Blo 1156638 1158267 := bstep (se 1 (by rfl) ⟨868700, by rfl⟩ : syracuseStep 1158267 = 1737401) B1737401
theorem B5942443 : Blo 1156638 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B1158319 : Blo 1156638 1158319 := bstep (se 1 (by rfl) ⟨868739, by rfl⟩ : syracuseStep 1158319 = 1737479) B1737479
theorem B1158343 : Blo 1156638 1158343 := bstep (se 1 (by rfl) ⟨868757, by rfl⟩ : syracuseStep 1158343 = 1737515) B1737515
theorem B1158363 : Blo 1156638 1158363 := bstep (se 1 (by rfl) ⟨868772, by rfl⟩ : syracuseStep 1158363 = 1737545) B1737545
theorem B4173047 : Blo 1156638 4173047 := bstep (se 1 (by rfl) ⟨3129785, by rfl⟩ : syracuseStep 4173047 = 6259571) B6259571
theorem B1158439 : Blo 1156638 1158439 := bstep (se 1 (by rfl) ⟨868829, by rfl⟩ : syracuseStep 1158439 = 1737659) B1737659
theorem B1158479 : Blo 1156638 1158479 := bstep (se 1 (by rfl) ⟨868859, by rfl⟩ : syracuseStep 1158479 = 1737719) B1737719
theorem B1158495 : Blo 1156638 1158495 := bstep (se 1 (by rfl) ⟨868871, by rfl⟩ : syracuseStep 1158495 = 1737743) B1737743
theorem B1158523 : Blo 1156638 1158523 := bstep (se 1 (by rfl) ⟨868892, by rfl⟩ : syracuseStep 1158523 = 1737785) B1737785
theorem B1158575 : Blo 1156638 1158575 := bstep (se 1 (by rfl) ⟨868931, by rfl⟩ : syracuseStep 1158575 = 1737863) B1737863
theorem B1158599 : Blo 1156638 1158599 := bstep (se 1 (by rfl) ⟨868949, by rfl⟩ : syracuseStep 1158599 = 1737899) B1737899
theorem B1158619 : Blo 1156638 1158619 := bstep (se 1 (by rfl) ⟨868964, by rfl⟩ : syracuseStep 1158619 = 1737929) B1737929
theorem B1158695 : Blo 1156638 1158695 := bstep (se 1 (by rfl) ⟨869021, by rfl⟩ : syracuseStep 1158695 = 1738043) B1738043
theorem B1158735 : Blo 1156638 1158735 := bstep (se 1 (by rfl) ⟨869051, by rfl⟩ : syracuseStep 1158735 = 1738103) B1738103
theorem B1158751 : Blo 1156638 1158751 := bstep (se 1 (by rfl) ⟨869063, by rfl⟩ : syracuseStep 1158751 = 1738127) B1738127
theorem B2928251 : Blo 1156638 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B1158779 : Blo 1156638 1158779 := bstep (se 1 (by rfl) ⟨869084, by rfl⟩ : syracuseStep 1158779 = 1738169) B1738169
theorem B1158831 : Blo 1156638 1158831 := bstep (se 1 (by rfl) ⟨869123, by rfl⟩ : syracuseStep 1158831 = 1738247) B1738247
theorem B1158855 : Blo 1156638 1158855 := bstep (se 1 (by rfl) ⟨869141, by rfl⟩ : syracuseStep 1158855 = 1738283) B1738283
theorem B1158875 : Blo 1156638 1158875 := bstep (se 1 (by rfl) ⟨869156, by rfl⟩ : syracuseStep 1158875 = 1738313) B1738313
theorem B1158951 : Blo 1156638 1158951 := bstep (se 1 (by rfl) ⟨869213, by rfl⟩ : syracuseStep 1158951 = 1738427) B1738427
theorem B3714859 : Blo 1156638 3714859 := bstep (se 1 (by rfl) ⟨2786144, by rfl⟩ : syracuseStep 3714859 = 5572289) B5572289
theorem B28159811 : Blo 1156638 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B1158991 : Blo 1156638 1158991 := bstep (se 1 (by rfl) ⟨869243, by rfl⟩ : syracuseStep 1158991 = 1738487) B1738487
theorem B1159007 : Blo 1156638 1159007 := bstep (se 1 (by rfl) ⟨869255, by rfl⟩ : syracuseStep 1159007 = 1738511) B1738511
theorem B1879915 : Blo 1156638 1879915 := bstep (se 1 (by rfl) ⟨1409936, by rfl⟩ : syracuseStep 1879915 = 2819873) B2819873
theorem B3911543 : Blo 1156638 3911543 := bstep (se 1 (by rfl) ⟨2933657, by rfl⟩ : syracuseStep 3911543 = 5867315) B5867315
theorem B1159035 : Blo 1156638 1159035 := bstep (se 1 (by rfl) ⟨869276, by rfl⟩ : syracuseStep 1159035 = 1738553) B1738553
theorem B2928545 : Blo 1156638 2928545 := bstep (se 2 (by rfl) ⟨1098204, by rfl⟩ : syracuseStep 2928545 = 2196409) B2196409
theorem B1159087 : Blo 1156638 1159087 := bstep (se 1 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 1159087 = 1738631) B1738631
theorem B1159111 : Blo 1156638 1159111 := bstep (se 1 (by rfl) ⟨869333, by rfl⟩ : syracuseStep 1159111 = 1738667) B1738667
theorem B1159131 : Blo 1156638 1159131 := bstep (se 1 (by rfl) ⟨869348, by rfl⟩ : syracuseStep 1159131 = 1738697) B1738697
theorem B3715091 : Blo 1156638 3715091 := bstep (se 1 (by rfl) ⟨2786318, by rfl⟩ : syracuseStep 3715091 = 5572637) B5572637
theorem B1159207 : Blo 1156638 1159207 := bstep (se 1 (by rfl) ⟨869405, by rfl⟩ : syracuseStep 1159207 = 1738811) B1738811
theorem B8794169 : Blo 1156638 8794169 := bstep (se 2 (by rfl) ⟨3297813, by rfl⟩ : syracuseStep 8794169 = 6595627) B6595627
theorem B3911759 : Blo 1156638 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B1159247 : Blo 1156638 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B4403281 : Blo 1156638 4403281 := bstep (se 2 (by rfl) ⟨1651230, by rfl⟩ : syracuseStep 4403281 = 3302461) B3302461
theorem B1159263 : Blo 1156638 1159263 := bstep (se 1 (by rfl) ⟨869447, by rfl⟩ : syracuseStep 1159263 = 1738895) B1738895
theorem B1159291 : Blo 1156638 1159291 := bstep (se 1 (by rfl) ⟨869468, by rfl⟩ : syracuseStep 1159291 = 1738937) B1738937
theorem B1159343 : Blo 1156638 1159343 := bstep (se 1 (by rfl) ⟨869507, by rfl⟩ : syracuseStep 1159343 = 1739015) B1739015
theorem B1159367 : Blo 1156638 1159367 := bstep (se 1 (by rfl) ⟨869525, by rfl⟩ : syracuseStep 1159367 = 1739051) B1739051
theorem B1159387 : Blo 1156638 1159387 := bstep (se 1 (by rfl) ⟨869540, by rfl⟩ : syracuseStep 1159387 = 1739081) B1739081
theorem B1159463 : Blo 1156638 1159463 := bstep (se 1 (by rfl) ⟨869597, by rfl⟩ : syracuseStep 1159463 = 1739195) B1739195
theorem B1159503 : Blo 1156638 1159503 := bstep (se 1 (by rfl) ⟨869627, by rfl⟩ : syracuseStep 1159503 = 1739255) B1739255
theorem B1159519 : Blo 1156638 1159519 := bstep (se 1 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 1159519 = 1739279) B1739279
theorem B1159547 : Blo 1156638 1159547 := bstep (se 1 (by rfl) ⟨869660, by rfl⟩ : syracuseStep 1159547 = 1739321) B1739321
theorem B4403585 : Blo 1156638 4403585 := bstep (se 2 (by rfl) ⟨1651344, by rfl⟩ : syracuseStep 4403585 = 3302689) B3302689
theorem B1159599 : Blo 1156638 1159599 := bstep (se 1 (by rfl) ⟨869699, by rfl⟩ : syracuseStep 1159599 = 1739399) B1739399
theorem B1159623 : Blo 1156638 1159623 := bstep (se 1 (by rfl) ⟨869717, by rfl⟩ : syracuseStep 1159623 = 1739435) B1739435
theorem B3912137 : Blo 1156638 3912137 := bstep (se 2 (by rfl) ⟨1467051, by rfl⟩ : syracuseStep 3912137 = 2934103) B2934103
theorem B1159643 : Blo 1156638 1159643 := bstep (se 1 (by rfl) ⟨869732, by rfl⟩ : syracuseStep 1159643 = 1739465) B1739465
theorem B10564121 : Blo 1156638 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B4174361 : Blo 1156638 4174361 := bstep (se 2 (by rfl) ⟨1565385, by rfl⟩ : syracuseStep 4174361 = 3130771) B3130771
theorem B2470439 : Blo 1156638 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B1159719 : Blo 1156638 1159719 := bstep (se 1 (by rfl) ⟨869789, by rfl⟩ : syracuseStep 1159719 = 1739579) B1739579
theorem B1159759 : Blo 1156638 1159759 := bstep (se 1 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 1159759 = 1739639) B1739639
theorem B1159775 : Blo 1156638 1159775 := bstep (se 1 (by rfl) ⟨869831, by rfl⟩ : syracuseStep 1159775 = 1739663) B1739663
theorem B1159803 : Blo 1156638 1159803 := bstep (se 1 (by rfl) ⟨869852, by rfl⟩ : syracuseStep 1159803 = 1739705) B1739705
theorem B3388043 : Blo 1156638 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B1159855 : Blo 1156638 1159855 := bstep (se 1 (by rfl) ⟨869891, by rfl⟩ : syracuseStep 1159855 = 1739783) B1739783
theorem B1159879 : Blo 1156638 1159879 := bstep (se 1 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 1159879 = 1739819) B1739819
theorem B3912407 : Blo 1156638 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B1159899 : Blo 1156638 1159899 := bstep (se 1 (by rfl) ⟨869924, by rfl⟩ : syracuseStep 1159899 = 1739849) B1739849
theorem B1159975 : Blo 1156638 1159975 := bstep (se 1 (by rfl) ⟨869981, by rfl⟩ : syracuseStep 1159975 = 1739963) B1739963
theorem B4404041 : Blo 1156638 4404041 := bstep (se 2 (by rfl) ⟨1651515, by rfl⟩ : syracuseStep 4404041 = 3303031) B3303031
theorem B1160015 : Blo 1156638 1160015 := bstep (se 1 (by rfl) ⟨870011, by rfl⟩ : syracuseStep 1160015 = 1740023) B1740023
theorem B1160031 : Blo 1156638 1160031 := bstep (se 1 (by rfl) ⟨870023, by rfl⟩ : syracuseStep 1160031 = 1740047) B1740047
theorem B1160059 : Blo 1156638 1160059 := bstep (se 1 (by rfl) ⟨870044, by rfl⟩ : syracuseStep 1160059 = 1740089) B1740089
theorem B3912623 : Blo 1156638 3912623 := bstep (se 1 (by rfl) ⟨2934467, by rfl⟩ : syracuseStep 3912623 = 5868935) B5868935
theorem B1160111 : Blo 1156638 1160111 := bstep (se 1 (by rfl) ⟨870083, by rfl⟩ : syracuseStep 1160111 = 1740167) B1740167
theorem B1160135 : Blo 1156638 1160135 := bstep (se 1 (by rfl) ⟨870101, by rfl⟩ : syracuseStep 1160135 = 1740203) B1740203
theorem B1160155 : Blo 1156638 1160155 := bstep (se 1 (by rfl) ⟨870116, by rfl⟩ : syracuseStep 1160155 = 1740233) B1740233
theorem B14857181 : Blo 1156638 14857181 := bstep (se 3 (by rfl) ⟨2785721, by rfl⟩ : syracuseStep 14857181 = 5571443) B5571443
theorem B4404239 : Blo 1156638 4404239 := bstep (se 1 (by rfl) ⟨3303179, by rfl⟩ : syracuseStep 4404239 = 6606359) B6606359
theorem B1160231 : Blo 1156638 1160231 := bstep (se 1 (by rfl) ⟨870173, by rfl⟩ : syracuseStep 1160231 = 1740347) B1740347
theorem B1160271 : Blo 1156638 1160271 := bstep (se 1 (by rfl) ⟨870203, by rfl⟩ : syracuseStep 1160271 = 1740407) B1740407
theorem B1160287 : Blo 1156638 1160287 := bstep (se 1 (by rfl) ⟨870215, by rfl⟩ : syracuseStep 1160287 = 1740431) B1740431
theorem B1160315 : Blo 1156638 1160315 := bstep (se 1 (by rfl) ⟨870236, by rfl⟩ : syracuseStep 1160315 = 1740473) B1740473
theorem B1160367 : Blo 1156638 1160367 := bstep (se 1 (by rfl) ⟨870275, by rfl⟩ : syracuseStep 1160367 = 1740551) B1740551
theorem B1160391 : Blo 1156638 1160391 := bstep (se 1 (by rfl) ⟨870293, by rfl⟩ : syracuseStep 1160391 = 1740587) B1740587
theorem B1160411 : Blo 1156638 1160411 := bstep (se 1 (by rfl) ⟨870308, by rfl⟩ : syracuseStep 1160411 = 1740617) B1740617
theorem B1160487 : Blo 1156638 1160487 := bstep (se 1 (by rfl) ⟨870365, by rfl⟩ : syracuseStep 1160487 = 1740731) B1740731
theorem B1160527 : Blo 1156638 1160527 := bstep (se 1 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 1160527 = 1740791) B1740791
theorem B1160543 : Blo 1156638 1160543 := bstep (se 1 (by rfl) ⟨870407, by rfl⟩ : syracuseStep 1160543 = 1740815) B1740815
theorem B1160571 : Blo 1156638 1160571 := bstep (se 1 (by rfl) ⟨870428, by rfl⟩ : syracuseStep 1160571 = 1740857) B1740857
theorem B1160623 : Blo 1156638 1160623 := bstep (se 1 (by rfl) ⟨870467, by rfl⟩ : syracuseStep 1160623 = 1740935) B1740935
theorem B1390007 : Blo 1156638 1390007 := bstep (se 1 (by rfl) ⟨1042505, by rfl⟩ : syracuseStep 1390007 = 2085011) B2085011
theorem B1652233 : Blo 1156638 1652233 := bstep (se 2 (by rfl) ⟨619587, by rfl⟩ : syracuseStep 1652233 = 1239175) B1239175
theorem B2930215 : Blo 1156638 2930215 := bstep (se 1 (by rfl) ⟨2197661, by rfl⟩ : syracuseStep 2930215 = 4395323) B4395323
theorem B3716705 : Blo 1156638 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B2602619 : Blo 1156638 2602619 := bstep (se 1 (by rfl) ⟨1951964, by rfl⟩ : syracuseStep 2602619 = 3903929) B3903929
theorem B1652347 : Blo 1156638 1652347 := bstep (se 1 (by rfl) ⟨1239260, by rfl⟩ : syracuseStep 1652347 = 2478521) B2478521
theorem B2602745 : Blo 1156638 2602745 := bstep (se 2 (by rfl) ⟨976029, by rfl⟩ : syracuseStep 2602745 = 1952059) B1952059
theorem B2930539 : Blo 1156638 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B8796113 : Blo 1156638 8796113 := bstep (se 2 (by rfl) ⟨3298542, by rfl⟩ : syracuseStep 8796113 = 6597085) B6597085
theorem B2603015 : Blo 1156638 2603015 := bstep (se 1 (by rfl) ⟨1952261, by rfl⟩ : syracuseStep 2603015 = 3904523) B3904523
theorem B2603087 : Blo 1156638 2603087 := bstep (se 1 (by rfl) ⟨1952315, by rfl⟩ : syracuseStep 2603087 = 3904631) B3904631
theorem B2603483 : Blo 1156638 2603483 := bstep (se 1 (by rfl) ⟨1952612, by rfl⟩ : syracuseStep 2603483 = 3905225) B3905225
theorem B2931187 : Blo 1156638 2931187 := bstep (se 1 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 2931187 = 4396781) B4396781
theorem B1981007 : Blo 1156638 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B2603951 : Blo 1156638 2603951 := bstep (se 1 (by rfl) ⟨1952963, by rfl⟩ : syracuseStep 2603951 = 3905927) B3905927
theorem B2604203 : Blo 1156638 2604203 := bstep (se 1 (by rfl) ⟨1953152, by rfl⟩ : syracuseStep 2604203 = 3906305) B3906305
theorem B3914999 : Blo 1156638 3914999 := bstep (se 1 (by rfl) ⟨2936249, by rfl⟩ : syracuseStep 3914999 = 5872499) B5872499
theorem B1883657 : Blo 1156638 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B3915323 : Blo 1156638 3915323 := bstep (se 1 (by rfl) ⟨2936492, by rfl⟩ : syracuseStep 3915323 = 5872985) B5872985
theorem B14270039 : Blo 1156638 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B2932321 : Blo 1156638 2932321 := bstep (se 2 (by rfl) ⟨1099620, by rfl⟩ : syracuseStep 2932321 = 2199241) B2199241
theorem B2604743 : Blo 1156638 2604743 := bstep (se 1 (by rfl) ⟨1953557, by rfl⟩ : syracuseStep 2604743 = 3907115) B3907115
theorem B3915593 : Blo 1156638 3915593 := bstep (se 2 (by rfl) ⟨1468347, by rfl⟩ : syracuseStep 3915593 = 2936695) B2936695
theorem B1982395 : Blo 1156638 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B12533939 : Blo 1156638 12533939 := bstep (se 1 (by rfl) ⟨9400454, by rfl⟩ : syracuseStep 12533939 = 18800909) B18800909
theorem B32096587 : Blo 1156638 32096587 := bstep (se 1 (by rfl) ⟨24072440, by rfl⟩ : syracuseStep 32096587 = 48144881) B48144881
theorem B7422313 : Blo 1156638 7422313 := bstep (se 2 (by rfl) ⟨2783367, by rfl⟩ : syracuseStep 7422313 = 5566735) B5566735
theorem B2933273 : Blo 1156638 2933273 := bstep (se 2 (by rfl) ⟨1099977, by rfl⟩ : syracuseStep 2933273 = 2199955) B2199955
theorem B2605607 : Blo 1156638 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B17810021 : Blo 1156638 17810021 := bstep (se 4 (by rfl) ⟨1669689, by rfl⟩ : syracuseStep 17810021 = 3339379) B3339379
theorem B3293885 : Blo 1156638 3293885 := bstep (se 3 (by rfl) ⟨617603, by rfl⟩ : syracuseStep 3293885 = 1235207) B1235207
theorem B2507593 : Blo 1156638 2507593 := bstep (se 2 (by rfl) ⟨940347, by rfl⟩ : syracuseStep 2507593 = 1880695) B1880695
theorem B2605931 : Blo 1156638 2605931 := bstep (se 1 (by rfl) ⟨1954448, by rfl⟩ : syracuseStep 2605931 = 3908897) B3908897
theorem B2605985 : Blo 1156638 2605985 := bstep (se 2 (by rfl) ⟨977244, by rfl⟩ : syracuseStep 2605985 = 1954489) B1954489
theorem B3916727 : Blo 1156638 3916727 := bstep (se 1 (by rfl) ⟨2937545, by rfl⟩ : syracuseStep 3916727 = 5875091) B5875091
theorem B3294215 : Blo 1156638 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B11289619 : Blo 1156638 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B2933779 : Blo 1156638 2933779 := bstep (se 1 (by rfl) ⟨2200334, by rfl⟩ : syracuseStep 2933779 = 4400669) B4400669
theorem B1983545 : Blo 1156638 1983545 := bstep (se 2 (by rfl) ⟨743829, by rfl⟩ : syracuseStep 1983545 = 1487659) B1487659
theorem B2606327 : Blo 1156638 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B2606921 : Blo 1156638 2606921 := bstep (se 2 (by rfl) ⟨977595, by rfl⟩ : syracuseStep 2606921 = 1955191) B1955191
theorem B2934863 : Blo 1156638 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B7424081 : Blo 1156638 7424081 := bstep (se 2 (by rfl) ⟨2784030, by rfl⟩ : syracuseStep 7424081 = 5568061) B5568061
theorem B14829911 : Blo 1156638 14829911 := bstep (se 1 (by rfl) ⟨11122433, by rfl⟩ : syracuseStep 14829911 = 22244867) B22244867
theorem B3131777 : Blo 1156638 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B36161977 : Blo 1156638 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B2607713 : Blo 1156638 2607713 := bstep (se 2 (by rfl) ⟨977892, by rfl⟩ : syracuseStep 2607713 = 1955785) B1955785
theorem B2935511 : Blo 1156638 2935511 := bstep (se 1 (by rfl) ⟨2201633, by rfl⟩ : syracuseStep 2935511 = 4403267) B4403267
theorem B7424797 : Blo 1156638 7424797 := bstep (se 3 (by rfl) ⟨1392149, by rfl⟩ : syracuseStep 7424797 = 2784299) B2784299
theorem B2476975 : Blo 1156638 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B1952687 : Blo 1156638 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B2608055 : Blo 1156638 2608055 := bstep (se 1 (by rfl) ⟨1956041, by rfl⟩ : syracuseStep 2608055 = 3912083) B3912083
theorem B2968595 : Blo 1156638 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B2935865 : Blo 1156638 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B10046711 : Blo 1156638 10046711 := bstep (se 1 (by rfl) ⟨7535033, by rfl⟩ : syracuseStep 10046711 = 15070067) B15070067
theorem B9882917 : Blo 1156638 9882917 := bstep (se 4 (by rfl) ⟨926523, by rfl⟩ : syracuseStep 9882917 = 1853047) B1853047
theorem B37604645 : Blo 1156638 37604645 := bstep (se 4 (by rfl) ⟨3525435, by rfl⟩ : syracuseStep 37604645 = 7050871) B7050871
theorem B14830937 : Blo 1156638 14830937 := bstep (se 2 (by rfl) ⟨5561601, by rfl⟩ : syracuseStep 14830937 = 11123203) B11123203
theorem B1953119 : Blo 1156638 1953119 := bstep (se 1 (by rfl) ⟨1464839, by rfl⟩ : syracuseStep 1953119 = 2929679) B2929679
theorem B60182003 : Blo 1156638 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B1854983 : Blo 1156638 1854983 := bstep (se 1 (by rfl) ⟨1391237, by rfl⟩ : syracuseStep 1854983 = 2782475) B2782475
theorem B2608649 : Blo 1156638 2608649 := bstep (se 2 (by rfl) ⟨978243, by rfl⟩ : syracuseStep 2608649 = 1956487) B1956487
theorem B3296983 : Blo 1156638 3296983 := bstep (se 1 (by rfl) ⟨2472737, by rfl⟩ : syracuseStep 3296983 = 4945475) B4945475
theorem B3297017 : Blo 1156638 3297017 := bstep (se 2 (by rfl) ⟨1236381, by rfl⟩ : syracuseStep 3297017 = 2472763) B2472763
theorem B2608991 : Blo 1156638 2608991 := bstep (se 1 (by rfl) ⟨1956743, by rfl⟩ : syracuseStep 2608991 = 3913487) B3913487
theorem B3297131 : Blo 1156638 3297131 := bstep (se 1 (by rfl) ⟨2472848, by rfl⟩ : syracuseStep 3297131 = 4945697) B4945697
theorem B4181869 : Blo 1156638 4181869 := bstep (se 3 (by rfl) ⟨784100, by rfl⟩ : syracuseStep 4181869 = 1568201) B1568201
theorem B1953679 : Blo 1156638 1953679 := bstep (se 1 (by rfl) ⟨1465259, by rfl⟩ : syracuseStep 1953679 = 2930519) B2930519
theorem B2969519 : Blo 1156638 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B3297199 : Blo 1156638 3297199 := bstep (se 1 (by rfl) ⟨2472899, by rfl⟩ : syracuseStep 3297199 = 4945799) B4945799
theorem B1855495 : Blo 1156638 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B2609171 : Blo 1156638 2609171 := bstep (se 1 (by rfl) ⟨1956878, by rfl⟩ : syracuseStep 2609171 = 3913757) B3913757
theorem B2117711 : Blo 1156638 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B2609513 : Blo 1156638 2609513 := bstep (se 2 (by rfl) ⟨978567, by rfl⟩ : syracuseStep 2609513 = 1957135) B1957135
theorem B1954361 : Blo 1156638 1954361 := bstep (se 2 (by rfl) ⟨732885, by rfl⟩ : syracuseStep 1954361 = 1465771) B1465771
theorem B1856123 : Blo 1156638 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B5952211 : Blo 1156638 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B2610107 : Blo 1156638 2610107 := bstep (se 1 (by rfl) ⟨1957580, by rfl⟩ : syracuseStep 2610107 = 3915161) B3915161
theorem B2610233 : Blo 1156638 2610233 := bstep (se 2 (by rfl) ⟨978837, by rfl⟩ : syracuseStep 2610233 = 1957675) B1957675
theorem B3298475 : Blo 1156638 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B1955063 : Blo 1156638 1955063 := bstep (se 1 (by rfl) ⟨1466297, by rfl⟩ : syracuseStep 1955063 = 2932595) B2932595
theorem B2610575 : Blo 1156638 2610575 := bstep (se 1 (by rfl) ⟨1957931, by rfl⟩ : syracuseStep 2610575 = 3915863) B3915863
theorem B2381239 : Blo 1156638 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B7427645 : Blo 1156638 7427645 := bstep (se 3 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 7427645 = 2785367) B2785367
theorem B1955407 : Blo 1156638 1955407 := bstep (se 1 (by rfl) ⟨1466555, by rfl⟩ : syracuseStep 1955407 = 2933111) B2933111
theorem B13194899 : Blo 1156638 13194899 := bstep (se 1 (by rfl) ⟨9896174, by rfl⟩ : syracuseStep 13194899 = 19792349) B19792349
theorem B2610899 : Blo 1156638 2610899 := bstep (se 1 (by rfl) ⟨1958174, by rfl⟩ : syracuseStep 2610899 = 3916349) B3916349
theorem B3135191 : Blo 1156638 3135191 := bstep (se 1 (by rfl) ⟨2351393, by rfl⟩ : syracuseStep 3135191 = 4702787) B4702787
theorem B1955657 : Blo 1156638 1955657 := bstep (se 2 (by rfl) ⟨733371, by rfl⟩ : syracuseStep 1955657 = 1466743) B1466743
theorem B6608749 : Blo 1156638 6608749 := bstep (se 3 (by rfl) ⟨1239140, by rfl⟩ : syracuseStep 6608749 = 2478281) B2478281
theorem B1464247 : Blo 1156638 1464247 := bstep (se 1 (by rfl) ⟨1098185, by rfl⟩ : syracuseStep 1464247 = 2196371) B2196371
theorem B14833601 : Blo 1156638 14833601 := bstep (se 2 (by rfl) ⟨5562600, by rfl⟩ : syracuseStep 14833601 = 11125201) B11125201
theorem B1956089 : Blo 1156638 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B9394481 : Blo 1156638 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B1956271 : Blo 1156638 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B1956359 : Blo 1156638 1956359 := bstep (se 1 (by rfl) ⟨1467269, by rfl⟩ : syracuseStep 1956359 = 2934539) B2934539
theorem B2972371 : Blo 1156638 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B1956703 : Blo 1156638 1956703 := bstep (se 1 (by rfl) ⟨1467527, by rfl⟩ : syracuseStep 1956703 = 2935055) B2935055
theorem B1760105 : Blo 1156638 1760105 := bstep (se 2 (by rfl) ⟨660039, by rfl⟩ : syracuseStep 1760105 = 1320079) B1320079
theorem B31742837 : Blo 1156638 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B1956791 : Blo 1156638 1956791 := bstep (se 1 (by rfl) ⟨1467593, by rfl⟩ : syracuseStep 1956791 = 2935187) B2935187
theorem B1301467 : Blo 1156638 1301467 := bstep (se 1 (by rfl) ⟨976100, by rfl⟩ : syracuseStep 1301467 = 1952201) B1952201
theorem B7527397 : Blo 1156638 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B11295787 : Blo 1156638 11295787 := bstep (se 1 (by rfl) ⟨8471840, by rfl⟩ : syracuseStep 11295787 = 16943681) B16943681
theorem B1465543 : Blo 1156638 1465543 := bstep (se 1 (by rfl) ⟨1099157, by rfl⟩ : syracuseStep 1465543 = 2198315) B2198315
theorem B50879735 : Blo 1156638 50879735 := bstep (se 1 (by rfl) ⟨38159801, by rfl⟩ : syracuseStep 50879735 = 76319603) B76319603
theorem B34331921 : Blo 1156638 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B1301935 : Blo 1156638 1301935 := bstep (se 1 (by rfl) ⟨976451, by rfl⟩ : syracuseStep 1301935 = 1952903) B1952903
theorem B8805833 : Blo 1156638 8805833 := bstep (se 2 (by rfl) ⟨3302187, by rfl⟩ : syracuseStep 8805833 = 6604375) B6604375
theorem B1957385 : Blo 1156638 1957385 := bstep (se 2 (by rfl) ⟨734019, by rfl⟩ : syracuseStep 1957385 = 1468039) B1468039
theorem B3301003 : Blo 1156638 3301003 := bstep (se 1 (by rfl) ⟨2475752, by rfl⟩ : syracuseStep 3301003 = 4951505) B4951505
theorem B1957547 : Blo 1156638 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B5562179 : Blo 1156638 5562179 := bstep (se 1 (by rfl) ⟨4171634, by rfl⟩ : syracuseStep 5562179 = 8343269) B8343269
theorem B1302367 : Blo 1156638 1302367 := bstep (se 1 (by rfl) ⟨976775, by rfl⟩ : syracuseStep 1302367 = 1953551) B1953551
theorem B1957945 : Blo 1156638 1957945 := bstep (se 2 (by rfl) ⟨734229, by rfl⟩ : syracuseStep 1957945 = 1468459) B1468459
theorem B1302727 : Blo 1156638 1302727 := bstep (se 1 (by rfl) ⟨977045, by rfl⟩ : syracuseStep 1302727 = 1954091) B1954091
theorem B1958087 : Blo 1156638 1958087 := bstep (se 1 (by rfl) ⟨1468565, by rfl⟩ : syracuseStep 1958087 = 2937131) B2937131
theorem B1958249 : Blo 1156638 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B4514503 : Blo 1156638 4514503 := bstep (se 1 (by rfl) ⟨3385877, by rfl⟩ : syracuseStep 4514503 = 6771755) B6771755
theorem B1303591 : Blo 1156638 1303591 := bstep (se 1 (by rfl) ⟨977693, by rfl⟩ : syracuseStep 1303591 = 1955387) B1955387
theorem B1467983 : Blo 1156638 1467983 := bstep (se 1 (by rfl) ⟨1100987, by rfl⟩ : syracuseStep 1467983 = 2201975) B2201975
theorem B14838065 : Blo 1156638 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B1305211 : Blo 1156638 1305211 := bstep (se 1 (by rfl) ⟨978908, by rfl⟩ : syracuseStep 1305211 = 1957817) B1957817
theorem B5860025 : Blo 1156638 5860025 := bstep (se 2 (by rfl) ⟨2197509, by rfl⟩ : syracuseStep 5860025 = 4395019) B4395019
theorem B3304147 : Blo 1156638 3304147 := bstep (se 1 (by rfl) ⟨2478110, by rfl⟩ : syracuseStep 3304147 = 4956221) B4956221
theorem B9890707 : Blo 1156638 9890707 := bstep (se 1 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 9890707 = 14836061) B14836061
theorem B9399347 : Blo 1156638 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B1305679 : Blo 1156638 1305679 := bstep (se 1 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 1305679 = 1958519) B1958519
theorem B4452029 : Blo 1156638 4452029 := bstep (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) B1669511
theorem B3862379 : Blo 1156638 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B3567521 : Blo 1156638 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B4943987 : Blo 1156638 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B3764875 : Blo 1156638 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B14087339 : Blo 1156638 14087339 := bstep (se 1 (by rfl) ⟨10565504, by rfl⟩ : syracuseStep 14087339 = 21131009) B21131009
theorem B7435435 : Blo 1156638 7435435 := bstep (se 1 (by rfl) ⟨5576576, by rfl⟩ : syracuseStep 7435435 = 11153153) B11153153
theorem B23753999 : Blo 1156638 23753999 := bstep (se 1 (by rfl) ⟨17815499, by rfl⟩ : syracuseStep 23753999 = 35630999) B35630999
theorem B52917745 : Blo 1156638 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B7435921 : Blo 1156638 7435921 := bstep (se 2 (by rfl) ⟨2788470, by rfl⟩ : syracuseStep 7435921 = 5576941) B5576941
theorem B142571249 : Blo 1156638 142571249 := bstep (se 2 (by rfl) ⟨53464218, by rfl⟩ : syracuseStep 142571249 = 106928437) B106928437
theorem B9533371 : Blo 1156638 9533371 := bstep (se 1 (by rfl) ⟨7150028, by rfl⟩ : syracuseStep 9533371 = 14300057) B14300057
theorem B1735007 : Blo 1156638 1735007 := bstep (se 1 (by rfl) ⟨1301255, by rfl⟩ : syracuseStep 1735007 = 2602511) B2602511
theorem B1735019 : Blo 1156638 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B15038905 : Blo 1156638 15038905 := bstep (se 2 (by rfl) ⟨5639589, by rfl⟩ : syracuseStep 15038905 = 11279179) B11279179
theorem B1735247 : Blo 1156638 1735247 := bstep (se 1 (by rfl) ⟨1301435, by rfl⟩ : syracuseStep 1735247 = 2602871) B2602871
theorem B1735367 : Blo 1156638 1735367 := bstep (se 1 (by rfl) ⟨1301525, by rfl⟩ : syracuseStep 1735367 = 2603051) B2603051
theorem B1735529 : Blo 1156638 1735529 := bstep (se 2 (by rfl) ⟨650823, by rfl⟩ : syracuseStep 1735529 = 1301647) B1301647
theorem B1735607 : Blo 1156638 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B1735643 : Blo 1156638 1735643 := bstep (se 1 (by rfl) ⟨1301732, by rfl⟩ : syracuseStep 1735643 = 2603465) B2603465
theorem B15858767 : Blo 1156638 15858767 := bstep (se 1 (by rfl) ⟨11894075, by rfl⟩ : syracuseStep 15858767 = 23788151) B23788151
theorem B4947115 : Blo 1156638 4947115 := bstep (se 1 (by rfl) ⟨3710336, by rfl⟩ : syracuseStep 4947115 = 7420673) B7420673
theorem B1736111 : Blo 1156638 1736111 := bstep (se 1 (by rfl) ⟨1302083, by rfl⟩ : syracuseStep 1736111 = 2604167) B2604167
theorem B1736201 : Blo 1156638 1736201 := bstep (se 2 (by rfl) ⟨651075, by rfl⟩ : syracuseStep 1736201 = 1302151) B1302151
theorem B1736231 : Blo 1156638 1736231 := bstep (se 1 (by rfl) ⟨1302173, by rfl⟩ : syracuseStep 1736231 = 2604347) B2604347
theorem B1736315 : Blo 1156638 1736315 := bstep (se 1 (by rfl) ⟨1302236, by rfl⟩ : syracuseStep 1736315 = 2604473) B2604473
theorem B1736441 : Blo 1156638 1736441 := bstep (se 2 (by rfl) ⟨651165, by rfl⟩ : syracuseStep 1736441 = 1302331) B1302331
theorem B5865209 : Blo 1156638 5865209 := bstep (se 2 (by rfl) ⟨2199453, by rfl⟩ : syracuseStep 5865209 = 4398907) B4398907
theorem B1736543 : Blo 1156638 1736543 := bstep (se 1 (by rfl) ⟨1302407, by rfl⟩ : syracuseStep 1736543 = 2604815) B2604815
theorem B1736555 : Blo 1156638 1736555 := bstep (se 1 (by rfl) ⟨1302416, by rfl⟩ : syracuseStep 1736555 = 2604833) B2604833
theorem B56361041 : Blo 1156638 56361041 := bstep (se 2 (by rfl) ⟨21135390, by rfl⟩ : syracuseStep 56361041 = 42270781) B42270781
theorem B4948073 : Blo 1156638 4948073 := bstep (se 2 (by rfl) ⟨1855527, by rfl⟩ : syracuseStep 4948073 = 3711055) B3711055
theorem B8355959 : Blo 1156638 8355959 := bstep (se 1 (by rfl) ⟨6266969, by rfl⟩ : syracuseStep 8355959 = 12533939) B12533939
theorem B1736969 : Blo 1156638 1736969 := bstep (se 2 (by rfl) ⟨651363, by rfl⟩ : syracuseStep 1736969 = 1302727) B1302727
theorem B1737071 : Blo 1156638 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B42795449 : Blo 1156638 42795449 := bstep (se 2 (by rfl) ⟨16048293, by rfl⟩ : syracuseStep 42795449 = 32096587) B32096587
theorem B2195923 : Blo 1156638 2195923 := bstep (se 1 (by rfl) ⟨1646942, by rfl⟩ : syracuseStep 2195923 = 3293885) B3293885
theorem B9896417 : Blo 1156638 9896417 := bstep (se 2 (by rfl) ⟨3711156, by rfl⟩ : syracuseStep 9896417 = 7422313) B7422313
theorem B1737287 : Blo 1156638 1737287 := bstep (se 1 (by rfl) ⟨1302965, by rfl⟩ : syracuseStep 1737287 = 2605931) B2605931
theorem B1737323 : Blo 1156638 1737323 := bstep (se 1 (by rfl) ⟨1302992, by rfl⟩ : syracuseStep 1737323 = 2605985) B2605985
theorem B2196143 : Blo 1156638 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B21168965 : Blo 1156638 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B1737551 : Blo 1156638 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B3343457 : Blo 1156638 3343457 := bstep (se 2 (by rfl) ⟨1253796, by rfl⟩ : syracuseStep 3343457 = 2507593) B2507593
theorem B1737947 : Blo 1156638 1737947 := bstep (se 1 (by rfl) ⟨1303460, by rfl⟩ : syracuseStep 1737947 = 2606921) B2606921
theorem B2196713 : Blo 1156638 2196713 := bstep (se 2 (by rfl) ⟨823767, by rfl⟩ : syracuseStep 2196713 = 1647535) B1647535
theorem B1738121 : Blo 1156638 1738121 := bstep (se 2 (by rfl) ⟨651795, by rfl⟩ : syracuseStep 1738121 = 1303591) B1303591
theorem B4949387 : Blo 1156638 4949387 := bstep (se 1 (by rfl) ⟨3712040, by rfl⟩ : syracuseStep 4949387 = 7424081) B7424081
theorem B6587837 : Blo 1156638 6587837 := bstep (se 3 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 6587837 = 2470439) B2470439
theorem B7046689 : Blo 1156638 7046689 := bstep (se 2 (by rfl) ⟨2642508, by rfl⟩ : syracuseStep 7046689 = 5285017) B5285017
theorem B1738475 : Blo 1156638 1738475 := bstep (se 1 (by rfl) ⟨1303856, by rfl⟩ : syracuseStep 1738475 = 2607713) B2607713
theorem B1738703 : Blo 1156638 1738703 := bstep (se 1 (by rfl) ⟨1304027, by rfl⟩ : syracuseStep 1738703 = 2608055) B2608055
theorem B6588611 : Blo 1156638 6588611 := bstep (se 1 (by rfl) ⟨4941458, by rfl⟩ : syracuseStep 6588611 = 9882917) B9882917
theorem B25069763 : Blo 1156638 25069763 := bstep (se 1 (by rfl) ⟨18802322, by rfl⟩ : syracuseStep 25069763 = 37604645) B37604645
theorem B5867801 : Blo 1156638 5867801 := bstep (se 2 (by rfl) ⟨2200425, by rfl⟩ : syracuseStep 5867801 = 4400851) B4400851
theorem B1739099 : Blo 1156638 1739099 := bstep (se 1 (by rfl) ⟨1304324, by rfl⟩ : syracuseStep 1739099 = 2608649) B2608649
theorem B2198011 : Blo 1156638 2198011 := bstep (se 1 (by rfl) ⟨1648508, by rfl⟩ : syracuseStep 2198011 = 3297017) B3297017
theorem B1739327 : Blo 1156638 1739327 := bstep (se 1 (by rfl) ⟨1304495, by rfl⟩ : syracuseStep 1739327 = 2608991) B2608991
theorem B2198087 : Blo 1156638 2198087 := bstep (se 1 (by rfl) ⟨1648565, by rfl⟩ : syracuseStep 2198087 = 3297131) B3297131
theorem B1739447 : Blo 1156638 1739447 := bstep (se 1 (by rfl) ⟨1304585, by rfl⟩ : syracuseStep 1739447 = 2609171) B2609171
theorem B1411807 : Blo 1156638 1411807 := bstep (se 1 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 1411807 = 2117711) B2117711
theorem B5573519 : Blo 1156638 5573519 := bstep (se 1 (by rfl) ⟨4180139, by rfl⟩ : syracuseStep 5573519 = 8360279) B8360279
theorem B1739675 : Blo 1156638 1739675 := bstep (se 1 (by rfl) ⟨1304756, by rfl⟩ : syracuseStep 1739675 = 2609513) B2609513
theorem B8784935 : Blo 1156638 8784935 := bstep (se 1 (by rfl) ⟨6588701, by rfl⟩ : syracuseStep 8784935 = 13177403) B13177403
theorem B101682377 : Blo 1156638 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B1740071 : Blo 1156638 1740071 := bstep (se 1 (by rfl) ⟨1305053, by rfl⟩ : syracuseStep 1740071 = 2610107) B2610107
theorem B1740155 : Blo 1156638 1740155 := bstep (se 1 (by rfl) ⟨1305116, by rfl⟩ : syracuseStep 1740155 = 2610233) B2610233
theorem B2198983 : Blo 1156638 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B1740281 : Blo 1156638 1740281 := bstep (se 2 (by rfl) ⟨652605, by rfl⟩ : syracuseStep 1740281 = 1305211) B1305211
theorem B1740383 : Blo 1156638 1740383 := bstep (se 1 (by rfl) ⟨1305287, by rfl⟩ : syracuseStep 1740383 = 2610575) B2610575
theorem B9899729 : Blo 1156638 9899729 := bstep (se 2 (by rfl) ⟨3712398, by rfl⟩ : syracuseStep 9899729 = 7424797) B7424797
theorem B4951763 : Blo 1156638 4951763 := bstep (se 1 (by rfl) ⟨3713822, by rfl⟩ : syracuseStep 4951763 = 7427645) B7427645
theorem B1740599 : Blo 1156638 1740599 := bstep (se 1 (by rfl) ⟨1305449, by rfl⟩ : syracuseStep 1740599 = 2610899) B2610899
theorem B3706685 : Blo 1156638 3706685 := bstep (se 3 (by rfl) ⟨695003, by rfl⟩ : syracuseStep 3706685 = 1390007) B1390007
theorem B1740905 : Blo 1156638 1740905 := bstep (se 2 (by rfl) ⟨652839, by rfl⟩ : syracuseStep 1740905 = 1305679) B1305679
theorem B8360509 : Blo 1156638 8360509 := bstep (se 3 (by rfl) ⟨1567595, by rfl⟩ : syracuseStep 8360509 = 3135191) B3135191
theorem B33919823 : Blo 1156638 33919823 := bstep (se 1 (by rfl) ⟨25439867, by rfl⟩ : syracuseStep 33919823 = 50879735) B50879735
theorem B4395977 : Blo 1156638 4395977 := bstep (se 2 (by rfl) ⟨1648491, by rfl⟩ : syracuseStep 4395977 = 3296983) B3296983
theorem B5870555 : Blo 1156638 5870555 := bstep (se 1 (by rfl) ⟨4402916, by rfl⟩ : syracuseStep 5870555 = 8805833) B8805833
theorem B5575655 : Blo 1156638 5575655 := bstep (se 1 (by rfl) ⟨4181741, by rfl⟩ : syracuseStep 5575655 = 8363483) B8363483
theorem B4953145 : Blo 1156638 4953145 := bstep (se 2 (by rfl) ⟨1857429, by rfl⟩ : syracuseStep 4953145 = 3714859) B3714859
theorem B5870717 : Blo 1156638 5870717 := bstep (se 3 (by rfl) ⟨1100759, by rfl⟩ : syracuseStep 5870717 = 2201519) B2201519
theorem B5575825 : Blo 1156638 5575825 := bstep (se 2 (by rfl) ⟨2090934, by rfl⟩ : syracuseStep 5575825 = 4181869) B4181869
theorem B3708119 : Blo 1156638 3708119 := bstep (se 1 (by rfl) ⟨2781089, by rfl⟩ : syracuseStep 3708119 = 5562179) B5562179
theorem B4396265 : Blo 1156638 4396265 := bstep (se 2 (by rfl) ⟨1648599, by rfl⟩ : syracuseStep 4396265 = 3297199) B3297199
theorem B5575979 : Blo 1156638 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B4396477 : Blo 1156638 4396477 := bstep (se 3 (by rfl) ⟨824339, by rfl⟩ : syracuseStep 4396477 = 1648679) B1648679
theorem B5871041 : Blo 1156638 5871041 := bstep (se 2 (by rfl) ⟨2201640, by rfl⟩ : syracuseStep 5871041 = 4403281) B4403281
theorem B5576327 : Blo 1156638 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B5019833 : Blo 1156638 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B3906683 : Blo 1156638 3906683 := bstep (se 1 (by rfl) ⟨2930012, by rfl⟩ : syracuseStep 3906683 = 5860025) B5860025
theorem B70556993 : Blo 1156638 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B2202977 : Blo 1156638 2202977 := bstep (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) B1652233
theorem B6266231 : Blo 1156638 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B3906953 : Blo 1156638 3906953 := bstep (se 2 (by rfl) ⟨1465107, by rfl⟩ : syracuseStep 3906953 = 2930215) B2930215
theorem B38149541 : Blo 1156638 38149541 := bstep (se 4 (by rfl) ⟨3576519, by rfl⟩ : syracuseStep 38149541 = 7153039) B7153039
theorem B2203129 : Blo 1156638 2203129 := bstep (se 2 (by rfl) ⟨826173, by rfl⟩ : syracuseStep 2203129 = 1652347) B1652347
theorem B11148961 : Blo 1156638 11148961 := bstep (se 2 (by rfl) ⟨4180860, by rfl⟩ : syracuseStep 11148961 = 8361721) B8361721
theorem B3907385 : Blo 1156638 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B9904787 : Blo 1156638 9904787 := bstep (se 1 (by rfl) ⟨7428590, by rfl⟩ : syracuseStep 9904787 = 14857181) B14857181
theorem B3908249 : Blo 1156638 3908249 := bstep (se 2 (by rfl) ⟨1465593, by rfl⟩ : syracuseStep 3908249 = 2931187) B2931187
theorem B15835999 : Blo 1156638 15835999 := bstep (se 1 (by rfl) ⟨11876999, by rfl⟩ : syracuseStep 15835999 = 23753999) B23753999
theorem B10036529 : Blo 1156638 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B6596153 : Blo 1156638 6596153 := bstep (se 2 (by rfl) ⟨2473557, by rfl⟩ : syracuseStep 6596153 = 4947115) B4947115
theorem B1156671 : Blo 1156638 1156671 := bstep (se 1 (by rfl) ⟨867503, by rfl⟩ : syracuseStep 1156671 = 1735007) B1735007
theorem B1156679 : Blo 1156638 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B1156831 : Blo 1156638 1156831 := bstep (se 1 (by rfl) ⟨867623, by rfl⟩ : syracuseStep 1156831 = 1735247) B1735247
theorem B1320671 : Blo 1156638 1320671 := bstep (se 1 (by rfl) ⟨990503, by rfl⟩ : syracuseStep 1320671 = 1981007) B1981007
theorem B1156911 : Blo 1156638 1156911 := bstep (se 1 (by rfl) ⟨867683, by rfl⟩ : syracuseStep 1156911 = 1735367) B1735367
theorem B1157019 : Blo 1156638 1157019 := bstep (se 1 (by rfl) ⟨867764, by rfl⟩ : syracuseStep 1157019 = 1735529) B1735529
theorem B1157071 : Blo 1156638 1157071 := bstep (se 1 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 1157071 = 1735607) B1735607
theorem B1157095 : Blo 1156638 1157095 := bstep (se 1 (by rfl) ⟨867821, by rfl⟩ : syracuseStep 1157095 = 1735643) B1735643
theorem B3909761 : Blo 1156638 3909761 := bstep (se 2 (by rfl) ⟨1466160, by rfl⟩ : syracuseStep 3909761 = 2932321) B2932321
theorem B4401337 : Blo 1156638 4401337 := bstep (se 2 (by rfl) ⟨1650501, by rfl⟩ : syracuseStep 4401337 = 3301003) B3301003
theorem B1157407 : Blo 1156638 1157407 := bstep (se 1 (by rfl) ⟨868055, by rfl⟩ : syracuseStep 1157407 = 1736111) B1736111
theorem B1157467 : Blo 1156638 1157467 := bstep (se 1 (by rfl) ⟨868100, by rfl⟩ : syracuseStep 1157467 = 1736201) B1736201
theorem B1255771 : Blo 1156638 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B1157487 : Blo 1156638 1157487 := bstep (se 1 (by rfl) ⟨868115, by rfl⟩ : syracuseStep 1157487 = 1736231) B1736231
theorem B9513359 : Blo 1156638 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B1157543 : Blo 1156638 1157543 := bstep (se 1 (by rfl) ⟨868157, by rfl⟩ : syracuseStep 1157543 = 1736315) B1736315
theorem B9513389 : Blo 1156638 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B1157627 : Blo 1156638 1157627 := bstep (se 1 (by rfl) ⟨868220, by rfl⟩ : syracuseStep 1157627 = 1736441) B1736441
theorem B3910139 : Blo 1156638 3910139 := bstep (se 1 (by rfl) ⟨2932604, by rfl⟩ : syracuseStep 3910139 = 5865209) B5865209
theorem B1157695 : Blo 1156638 1157695 := bstep (se 1 (by rfl) ⟨868271, by rfl⟩ : syracuseStep 1157695 = 1736543) B1736543
theorem B1157703 : Blo 1156638 1157703 := bstep (se 1 (by rfl) ⟨868277, by rfl⟩ : syracuseStep 1157703 = 1736555) B1736555
theorem B1157855 : Blo 1156638 1157855 := bstep (se 1 (by rfl) ⟨868391, by rfl⟩ : syracuseStep 1157855 = 1736783) B1736783
theorem B1157935 : Blo 1156638 1157935 := bstep (se 1 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 1157935 = 1736903) B1736903
theorem B1158043 : Blo 1156638 1158043 := bstep (se 1 (by rfl) ⟨868532, by rfl⟩ : syracuseStep 1158043 = 1737065) B1737065
theorem B3910571 : Blo 1156638 3910571 := bstep (se 1 (by rfl) ⟨2932928, by rfl⟩ : syracuseStep 3910571 = 5865857) B5865857
theorem B1158095 : Blo 1156638 1158095 := bstep (se 1 (by rfl) ⟨868571, by rfl⟩ : syracuseStep 1158095 = 1737143) B1737143
theorem B1158119 : Blo 1156638 1158119 := bstep (se 1 (by rfl) ⟨868589, by rfl⟩ : syracuseStep 1158119 = 1737179) B1737179
theorem B11873347 : Blo 1156638 11873347 := bstep (se 1 (by rfl) ⟨8905010, by rfl⟩ : syracuseStep 11873347 = 17810021) B17810021
theorem B5287027 : Blo 1156638 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B1158431 : Blo 1156638 1158431 := bstep (se 1 (by rfl) ⟨868823, by rfl⟩ : syracuseStep 1158431 = 1737647) B1737647
theorem B1158491 : Blo 1156638 1158491 := bstep (se 1 (by rfl) ⟨868868, by rfl⟩ : syracuseStep 1158491 = 1737737) B1737737
theorem B1158511 : Blo 1156638 1158511 := bstep (se 1 (by rfl) ⟨868883, by rfl⟩ : syracuseStep 1158511 = 1737767) B1737767
theorem B1322363 : Blo 1156638 1322363 := bstep (se 1 (by rfl) ⟨991772, by rfl⟩ : syracuseStep 1322363 = 1983545) B1983545
theorem B1158567 : Blo 1156638 1158567 := bstep (se 1 (by rfl) ⟨868925, by rfl⟩ : syracuseStep 1158567 = 1737851) B1737851
theorem B2928059 : Blo 1156638 2928059 := bstep (se 1 (by rfl) ⟨2196044, by rfl⟩ : syracuseStep 2928059 = 4392089) B4392089
theorem B3911111 : Blo 1156638 3911111 := bstep (se 1 (by rfl) ⟨2933333, by rfl⟩ : syracuseStep 3911111 = 5866667) B5866667
theorem B1158651 : Blo 1156638 1158651 := bstep (se 1 (by rfl) ⟨868988, by rfl⟩ : syracuseStep 1158651 = 1737977) B1737977
theorem B1158719 : Blo 1156638 1158719 := bstep (se 1 (by rfl) ⟨869039, by rfl⟩ : syracuseStep 1158719 = 1738079) B1738079
theorem B1158727 : Blo 1156638 1158727 := bstep (se 1 (by rfl) ⟨869045, by rfl⟩ : syracuseStep 1158727 = 1738091) B1738091
theorem B1158879 : Blo 1156638 1158879 := bstep (se 1 (by rfl) ⟨869159, by rfl⟩ : syracuseStep 1158879 = 1738319) B1738319
theorem B3911435 : Blo 1156638 3911435 := bstep (se 1 (by rfl) ⟨2933576, by rfl⟩ : syracuseStep 3911435 = 5867153) B5867153
theorem B1158959 : Blo 1156638 1158959 := bstep (se 1 (by rfl) ⟨869219, by rfl⟩ : syracuseStep 1158959 = 1738439) B1738439
theorem B1159067 : Blo 1156638 1159067 := bstep (se 1 (by rfl) ⟨869300, by rfl⟩ : syracuseStep 1159067 = 1738601) B1738601
theorem B1159119 : Blo 1156638 1159119 := bstep (se 1 (by rfl) ⟨869339, by rfl⟩ : syracuseStep 1159119 = 1738679) B1738679
theorem B1159143 : Blo 1156638 1159143 := bstep (se 1 (by rfl) ⟨869357, by rfl⟩ : syracuseStep 1159143 = 1738715) B1738715
theorem B15052825 : Blo 1156638 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B3911705 : Blo 1156638 3911705 := bstep (se 2 (by rfl) ⟨1466889, by rfl⟩ : syracuseStep 3911705 = 2933779) B2933779
theorem B1159455 : Blo 1156638 1159455 := bstep (se 1 (by rfl) ⟨869591, by rfl⟩ : syracuseStep 1159455 = 1739183) B1739183
theorem B1159515 : Blo 1156638 1159515 := bstep (se 1 (by rfl) ⟨869636, by rfl⟩ : syracuseStep 1159515 = 1739273) B1739273
theorem B1159535 : Blo 1156638 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B1159591 : Blo 1156638 1159591 := bstep (se 1 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 1159591 = 1739387) B1739387
theorem B1159675 : Blo 1156638 1159675 := bstep (se 1 (by rfl) ⟨869756, by rfl⟩ : syracuseStep 1159675 = 1739513) B1739513
theorem B1159743 : Blo 1156638 1159743 := bstep (se 1 (by rfl) ⟨869807, by rfl⟩ : syracuseStep 1159743 = 1739615) B1739615
theorem B2929223 : Blo 1156638 2929223 := bstep (se 1 (by rfl) ⟨2196917, by rfl⟩ : syracuseStep 2929223 = 4393835) B4393835
theorem B1159751 : Blo 1156638 1159751 := bstep (se 1 (by rfl) ⟨869813, by rfl⟩ : syracuseStep 1159751 = 1739627) B1739627
theorem B1979063 : Blo 1156638 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B1159903 : Blo 1156638 1159903 := bstep (se 1 (by rfl) ⟨869927, by rfl⟩ : syracuseStep 1159903 = 1739855) B1739855
theorem B1159983 : Blo 1156638 1159983 := bstep (se 1 (by rfl) ⟨869987, by rfl⟩ : syracuseStep 1159983 = 1739975) B1739975
theorem B1160091 : Blo 1156638 1160091 := bstep (se 1 (by rfl) ⟨870068, by rfl⟩ : syracuseStep 1160091 = 1740137) B1740137
theorem B1160143 : Blo 1156638 1160143 := bstep (se 1 (by rfl) ⟨870107, by rfl⟩ : syracuseStep 1160143 = 1740215) B1740215
theorem B1160167 : Blo 1156638 1160167 := bstep (se 1 (by rfl) ⟨870125, by rfl⟩ : syracuseStep 1160167 = 1740251) B1740251
theorem B40121335 : Blo 1156638 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B3912947 : Blo 1156638 3912947 := bstep (se 1 (by rfl) ⟨2934710, by rfl⟩ : syracuseStep 3912947 = 5869421) B5869421
theorem B1160479 : Blo 1156638 1160479 := bstep (se 1 (by rfl) ⟨870359, by rfl⟩ : syracuseStep 1160479 = 1740719) B1740719
theorem B1160539 : Blo 1156638 1160539 := bstep (se 1 (by rfl) ⟨870404, by rfl⟩ : syracuseStep 1160539 = 1740809) B1740809
theorem B3913055 : Blo 1156638 3913055 := bstep (se 1 (by rfl) ⟨2934791, by rfl⟩ : syracuseStep 3913055 = 5869583) B5869583
theorem B1160559 : Blo 1156638 1160559 := bstep (se 1 (by rfl) ⟨870419, by rfl⟩ : syracuseStep 1160559 = 1740839) B1740839
theorem B1160615 : Blo 1156638 1160615 := bstep (se 1 (by rfl) ⟨870461, by rfl⟩ : syracuseStep 1160615 = 1740923) B1740923
theorem B2602439 : Blo 1156638 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B2602799 : Blo 1156638 2602799 := bstep (se 1 (by rfl) ⟨1952099, by rfl⟩ : syracuseStep 2602799 = 3904199) B3904199
theorem B2930489 : Blo 1156638 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B48215969 : Blo 1156638 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B4405529 : Blo 1156638 4405529 := bstep (se 2 (by rfl) ⟨1652073, by rfl⟩ : syracuseStep 4405529 = 3304147) B3304147
theorem B2603375 : Blo 1156638 2603375 := bstep (se 1 (by rfl) ⟨1952531, by rfl⟩ : syracuseStep 2603375 = 3905063) B3905063
theorem B2603447 : Blo 1156638 2603447 := bstep (se 1 (by rfl) ⟨1952585, by rfl⟩ : syracuseStep 2603447 = 3905171) B3905171
theorem B8796599 : Blo 1156638 8796599 := bstep (se 1 (by rfl) ⟨6597449, by rfl⟩ : syracuseStep 8796599 = 13194899) B13194899
theorem B13187609 : Blo 1156638 13187609 := bstep (se 2 (by rfl) ⟨4945353, by rfl⟩ : syracuseStep 13187609 = 9890707) B9890707
theorem B2603591 : Blo 1156638 2603591 := bstep (se 1 (by rfl) ⟨1952693, by rfl⟩ : syracuseStep 2603591 = 3905387) B3905387
theorem B2603627 : Blo 1156638 2603627 := bstep (se 1 (by rfl) ⟨1952720, by rfl⟩ : syracuseStep 2603627 = 3905441) B3905441
theorem B3914621 : Blo 1156638 3914621 := bstep (se 3 (by rfl) ⟨733991, by rfl⟩ : syracuseStep 3914621 = 1467983) B1467983
theorem B2604023 : Blo 1156638 2604023 := bstep (se 1 (by rfl) ⟨1953017, by rfl⟩ : syracuseStep 2604023 = 3906035) B3906035
theorem B25082909 : Blo 1156638 25082909 := bstep (se 3 (by rfl) ⟨4703045, by rfl⟩ : syracuseStep 25082909 = 9406091) B9406091
theorem B2931835 : Blo 1156638 2931835 := bstep (se 1 (by rfl) ⟨2198876, by rfl⟩ : syracuseStep 2931835 = 4397753) B4397753
theorem B3914891 : Blo 1156638 3914891 := bstep (se 1 (by rfl) ⟨2936168, by rfl⟩ : syracuseStep 3914891 = 5872337) B5872337
theorem B2604383 : Blo 1156638 2604383 := bstep (se 1 (by rfl) ⟨1953287, by rfl⟩ : syracuseStep 2604383 = 3906575) B3906575
theorem B5291513 : Blo 1156638 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B22887947 : Blo 1156638 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B2604779 : Blo 1156638 2604779 := bstep (se 1 (by rfl) ⟨1953584, by rfl⟩ : syracuseStep 2604779 = 3907169) B3907169
theorem B2506553 : Blo 1156638 2506553 := bstep (se 2 (by rfl) ⟨939957, by rfl⟩ : syracuseStep 2506553 = 1879915) B1879915
theorem B2604905 : Blo 1156638 2604905 := bstep (se 2 (by rfl) ⟨976839, by rfl⟩ : syracuseStep 2604905 = 1953679) B1953679
theorem B2473993 : Blo 1156638 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B2933243 : Blo 1156638 2933243 := bstep (se 1 (by rfl) ⟨2199932, by rfl⟩ : syracuseStep 2933243 = 4399865) B4399865
theorem B2605751 : Blo 1156638 2605751 := bstep (se 1 (by rfl) ⟨1954313, by rfl⟩ : syracuseStep 2605751 = 3908627) B3908627
theorem B3916511 : Blo 1156638 3916511 := bstep (se 1 (by rfl) ⟨2937383, by rfl⟩ : syracuseStep 3916511 = 5874767) B5874767
theorem B25051949 : Blo 1156638 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B2605967 : Blo 1156638 2605967 := bstep (se 1 (by rfl) ⟨1954475, by rfl⟩ : syracuseStep 2605967 = 3908951) B3908951
theorem B3916943 : Blo 1156638 3916943 := bstep (se 1 (by rfl) ⟨2937707, by rfl⟩ : syracuseStep 3916943 = 5875415) B5875415
theorem B6341777 : Blo 1156638 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B2934215 : Blo 1156638 2934215 := bstep (se 1 (by rfl) ⟨2200661, by rfl⟩ : syracuseStep 2934215 = 4401323) B4401323
theorem B2934265 : Blo 1156638 2934265 := bstep (se 2 (by rfl) ⟨1100349, by rfl⟩ : syracuseStep 2934265 = 2200699) B2200699
theorem B9913913 : Blo 1156638 9913913 := bstep (se 2 (by rfl) ⟨3717717, by rfl⟩ : syracuseStep 9913913 = 7435435) B7435435
theorem B2606687 : Blo 1156638 2606687 := bstep (se 1 (by rfl) ⟨1955015, by rfl⟩ : syracuseStep 2606687 = 3910031) B3910031
theorem B2934569 : Blo 1156638 2934569 := bstep (se 2 (by rfl) ⟨1100463, by rfl⟩ : syracuseStep 2934569 = 2200927) B2200927
theorem B2606903 : Blo 1156638 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B6604649 : Blo 1156638 6604649 := bstep (se 2 (by rfl) ⟨2476743, by rfl⟩ : syracuseStep 6604649 = 4953487) B4953487
theorem B2607209 : Blo 1156638 2607209 := bstep (se 2 (by rfl) ⟨977703, by rfl⟩ : syracuseStep 2607209 = 1955407) B1955407
theorem B2934913 : Blo 1156638 2934913 := bstep (se 2 (by rfl) ⟨1100592, by rfl⟩ : syracuseStep 2934913 = 2201185) B2201185
theorem B9914561 : Blo 1156638 9914561 := bstep (se 2 (by rfl) ⟨3717960, by rfl⟩ : syracuseStep 9914561 = 7435921) B7435921
theorem B16697609 : Blo 1156638 16697609 := bstep (se 2 (by rfl) ⟨6261603, by rfl⟩ : syracuseStep 16697609 = 12523207) B12523207
theorem B1952167 : Blo 1156638 1952167 := bstep (se 1 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 1952167 = 2928251) B2928251
theorem B2968019 : Blo 1156638 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B2574919 : Blo 1156638 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B1952329 : Blo 1156638 1952329 := bstep (se 2 (by rfl) ⟨732123, by rfl⟩ : syracuseStep 1952329 = 1464247) B1464247
theorem B2607695 : Blo 1156638 2607695 := bstep (se 1 (by rfl) ⟨1955771, by rfl⟩ : syracuseStep 2607695 = 3911543) B3911543
theorem B1952363 : Blo 1156638 1952363 := bstep (se 1 (by rfl) ⟨1464272, by rfl⟩ : syracuseStep 1952363 = 2928545) B2928545
theorem B2476727 : Blo 1156638 2476727 := bstep (se 1 (by rfl) ⟨1857545, by rfl⟩ : syracuseStep 2476727 = 3715091) B3715091
theorem B2607839 : Blo 1156638 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B3295991 : Blo 1156638 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B2935723 : Blo 1156638 2935723 := bstep (se 1 (by rfl) ⟨2201792, by rfl⟩ : syracuseStep 2935723 = 4403585) B4403585
theorem B2608091 : Blo 1156638 2608091 := bstep (se 1 (by rfl) ⟨1956068, by rfl⟩ : syracuseStep 2608091 = 3912137) B3912137
theorem B2608271 : Blo 1156638 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B2936027 : Blo 1156638 2936027 := bstep (se 1 (by rfl) ⟨2202020, by rfl⟩ : syracuseStep 2936027 = 4404041) B4404041
theorem B2608361 : Blo 1156638 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B2608415 : Blo 1156638 2608415 := bstep (se 1 (by rfl) ⟨1956311, by rfl⟩ : syracuseStep 2608415 = 3912623) B3912623
theorem B26791229 : Blo 1156638 26791229 := bstep (se 3 (by rfl) ⟨5023355, by rfl⟩ : syracuseStep 26791229 = 10046711) B10046711
theorem B2936159 : Blo 1156638 2936159 := bstep (se 1 (by rfl) ⟨2202119, by rfl⟩ : syracuseStep 2936159 = 4404239) B4404239
theorem B9391559 : Blo 1156638 9391559 := bstep (se 1 (by rfl) ⟨7043669, by rfl⟩ : syracuseStep 9391559 = 14087339) B14087339
theorem B2477803 : Blo 1156638 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B2608937 : Blo 1156638 2608937 := bstep (se 2 (by rfl) ⟨978351, by rfl⟩ : syracuseStep 2608937 = 1956703) B1956703
theorem B95047499 : Blo 1156638 95047499 := bstep (se 1 (by rfl) ⟨71285624, by rfl⟩ : syracuseStep 95047499 = 142571249) B142571249
theorem B2936857 : Blo 1156638 2936857 := bstep (se 2 (by rfl) ⟨1101321, by rfl⟩ : syracuseStep 2936857 = 2202643) B2202643
theorem B15061049 : Blo 1156638 15061049 := bstep (se 2 (by rfl) ⟨5647893, by rfl⟩ : syracuseStep 15061049 = 11295787) B11295787
theorem B1954057 : Blo 1156638 1954057 := bstep (se 2 (by rfl) ⟨732771, by rfl⟩ : syracuseStep 1954057 = 1465543) B1465543
theorem B2937161 : Blo 1156638 2937161 := bstep (se 2 (by rfl) ⟨1101435, by rfl⟩ : syracuseStep 2937161 = 2202871) B2202871
theorem B10572511 : Blo 1156638 10572511 := bstep (se 1 (by rfl) ⟨7929383, by rfl⟩ : syracuseStep 10572511 = 15858767) B15858767
theorem B2609999 : Blo 1156638 2609999 := bstep (se 1 (by rfl) ⟨1957499, by rfl⟩ : syracuseStep 2609999 = 3914999) B3914999
theorem B6607817 : Blo 1156638 6607817 := bstep (se 2 (by rfl) ⟨2477931, by rfl⟩ : syracuseStep 6607817 = 4955863) B4955863
theorem B2610215 : Blo 1156638 2610215 := bstep (se 1 (by rfl) ⟨1957661, by rfl⟩ : syracuseStep 2610215 = 3915323) B3915323
theorem B7918717 : Blo 1156638 7918717 := bstep (se 3 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 7918717 = 2969519) B2969519
theorem B2610395 : Blo 1156638 2610395 := bstep (se 1 (by rfl) ⟨1957796, by rfl⟩ : syracuseStep 2610395 = 3915593) B3915593
theorem B2643193 : Blo 1156638 2643193 := bstep (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) B1982395
theorem B2610593 : Blo 1156638 2610593 := bstep (se 2 (by rfl) ⟨978972, by rfl⟩ : syracuseStep 2610593 = 1957945) B1957945
theorem B1955515 : Blo 1156638 1955515 := bstep (se 1 (by rfl) ⟨1466636, by rfl⟩ : syracuseStep 1955515 = 2933273) B2933273
theorem B7427771 : Blo 1156638 7427771 := bstep (se 1 (by rfl) ⟨5570828, by rfl⟩ : syracuseStep 7427771 = 11141657) B11141657
theorem B43439921 : Blo 1156638 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B2611151 : Blo 1156638 2611151 := bstep (se 1 (by rfl) ⟨1958363, by rfl⟩ : syracuseStep 2611151 = 3916727) B3916727
theorem B6019337 : Blo 1156638 6019337 := bstep (se 2 (by rfl) ⟨2257251, by rfl⟩ : syracuseStep 6019337 = 4514503) B4514503
theorem B1464743 : Blo 1156638 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B1464895 : Blo 1156638 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B7428671 : Blo 1156638 7428671 := bstep (se 1 (by rfl) ⟨5571503, by rfl⟩ : syracuseStep 7428671 = 11143007) B11143007
theorem B8346185 : Blo 1156638 8346185 := bstep (se 2 (by rfl) ⟨3129819, by rfl⟩ : syracuseStep 8346185 = 6259639) B6259639
theorem B22305455 : Blo 1156638 22305455 := bstep (se 1 (by rfl) ⟨16729091, by rfl⟩ : syracuseStep 22305455 = 33458183) B33458183
theorem B1956575 : Blo 1156638 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B1465067 : Blo 1156638 1465067 := bstep (se 1 (by rfl) ⟨1098800, by rfl⟩ : syracuseStep 1465067 = 2197601) B2197601
theorem B28170989 : Blo 1156638 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B3300115 : Blo 1156638 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B9886607 : Blo 1156638 9886607 := bstep (se 1 (by rfl) ⟨7414955, by rfl⟩ : syracuseStep 9886607 = 14829911) B14829911
theorem B2087851 : Blo 1156638 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B1957007 : Blo 1156638 1957007 := bstep (se 1 (by rfl) ⟨1467755, by rfl⟩ : syracuseStep 1957007 = 2935511) B2935511
theorem B183196853 : Blo 1156638 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B1301791 : Blo 1156638 1301791 := bstep (se 1 (by rfl) ⟨976343, by rfl⟩ : syracuseStep 1301791 = 1952687) B1952687
theorem B1957243 : Blo 1156638 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B65068505 : Blo 1156638 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B85679639 : Blo 1156638 85679639 := bstep (se 1 (by rfl) ⟨64259729, by rfl⟩ : syracuseStep 85679639 = 128519459) B128519459
theorem B9887291 : Blo 1156638 9887291 := bstep (se 1 (by rfl) ⟨7415468, by rfl⟩ : syracuseStep 9887291 = 14830937) B14830937
theorem B1302079 : Blo 1156638 1302079 := bstep (se 1 (by rfl) ⟨976559, by rfl⟩ : syracuseStep 1302079 = 1953119) B1953119
theorem B1236655 : Blo 1156638 1236655 := bstep (se 1 (by rfl) ⟨927491, by rfl⟩ : syracuseStep 1236655 = 1854983) B1854983
theorem B1466039 : Blo 1156638 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B1466191 : Blo 1156638 1466191 := bstep (se 1 (by rfl) ⟨1099643, by rfl⟩ : syracuseStep 1466191 = 2199287) B2199287
theorem B8806319 : Blo 1156638 8806319 := bstep (se 1 (by rfl) ⟨6604739, by rfl⟩ : syracuseStep 8806319 = 13209479) B13209479
theorem B5857433 : Blo 1156638 5857433 := bstep (se 2 (by rfl) ⟨2196537, by rfl⟩ : syracuseStep 5857433 = 4393075) B4393075
theorem B1302907 : Blo 1156638 1302907 := bstep (se 1 (by rfl) ⟨977180, by rfl⟩ : syracuseStep 1302907 = 1954361) B1954361
theorem B1237415 : Blo 1156638 1237415 := bstep (se 1 (by rfl) ⟨928061, by rfl⟩ : syracuseStep 1237415 = 1856123) B1856123
theorem B3170735 : Blo 1156638 3170735 := bstep (se 1 (by rfl) ⟨2378051, by rfl⟩ : syracuseStep 3170735 = 4756103) B4756103
theorem B1303375 : Blo 1156638 1303375 := bstep (se 1 (by rfl) ⟨977531, by rfl⟩ : syracuseStep 1303375 = 1955063) B1955063
theorem B4940639 : Blo 1156638 4940639 := bstep (se 1 (by rfl) ⟨3705479, by rfl⟩ : syracuseStep 4940639 = 7410959) B7410959
theorem B11887507 : Blo 1156638 11887507 := bstep (se 1 (by rfl) ⟨8915630, by rfl⟩ : syracuseStep 11887507 = 17831261) B17831261
theorem B5858243 : Blo 1156638 5858243 := bstep (se 1 (by rfl) ⟨4393682, by rfl⟩ : syracuseStep 5858243 = 8787365) B8787365
theorem B31745125 : Blo 1156638 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B1303771 : Blo 1156638 1303771 := bstep (se 1 (by rfl) ⟨977828, by rfl⟩ : syracuseStep 1303771 = 1955657) B1955657
theorem B3302633 : Blo 1156638 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B9889067 : Blo 1156638 9889067 := bstep (se 1 (by rfl) ⟨7416800, by rfl⟩ : syracuseStep 9889067 = 14833601) B14833601
theorem B96429491 : Blo 1156638 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B1304059 : Blo 1156638 1304059 := bstep (se 1 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 1304059 = 1956089) B1956089
theorem B7923257 : Blo 1156638 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B1304239 : Blo 1156638 1304239 := bstep (se 1 (by rfl) ⟨978179, by rfl⟩ : syracuseStep 1304239 = 1956359) B1956359
theorem B1173403 : Blo 1156638 1173403 := bstep (se 1 (by rfl) ⟨880052, by rfl⟩ : syracuseStep 1173403 = 1760105) B1760105
theorem B21161891 : Blo 1156638 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B1304527 : Blo 1156638 1304527 := bstep (se 1 (by rfl) ⟨978395, by rfl⟩ : syracuseStep 1304527 = 1956791) B1956791
theorem B1304923 : Blo 1156638 1304923 := bstep (se 1 (by rfl) ⟨978692, by rfl⟩ : syracuseStep 1304923 = 1957385) B1957385
theorem B1468783 : Blo 1156638 1468783 := bstep (se 1 (by rfl) ⟨1101587, by rfl⟩ : syracuseStep 1468783 = 2203175) B2203175
theorem B1305031 : Blo 1156638 1305031 := bstep (se 1 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 1305031 = 1957547) B1957547
theorem B2976335 : Blo 1156638 2976335 := bstep (se 1 (by rfl) ⟨2232251, by rfl⟩ : syracuseStep 2976335 = 4464503) B4464503
theorem B75066041 : Blo 1156638 75066041 := bstep (se 2 (by rfl) ⟨28149765, by rfl⟩ : syracuseStep 75066041 = 56299531) B56299531
theorem B1305391 : Blo 1156638 1305391 := bstep (se 1 (by rfl) ⟨979043, by rfl⟩ : syracuseStep 1305391 = 1958087) B1958087
theorem B1305499 : Blo 1156638 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B9892043 : Blo 1156638 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B12677491 : Blo 1156638 12677491 := bstep (se 1 (by rfl) ⟨9508118, by rfl⟩ : syracuseStep 12677491 = 19016237) B19016237
theorem B5861807 : Blo 1156638 5861807 := bstep (se 1 (by rfl) ⟨4396355, by rfl⟩ : syracuseStep 5861807 = 8792711) B8792711
theorem B3174985 : Blo 1156638 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B2716343 : Blo 1156638 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B2782031 : Blo 1156638 2782031 := bstep (se 1 (by rfl) ⟨2086523, by rfl⟩ : syracuseStep 2782031 = 4173047) B4173047
theorem B8811665 : Blo 1156638 8811665 := bstep (se 2 (by rfl) ⟨3304374, by rfl⟩ : syracuseStep 8811665 = 6608749) B6608749
theorem B18773207 : Blo 1156638 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B12711161 : Blo 1156638 12711161 := bstep (se 2 (by rfl) ⟨4766685, by rfl⟩ : syracuseStep 12711161 = 9533371) B9533371
theorem B5862779 : Blo 1156638 5862779 := bstep (se 1 (by rfl) ⟨4397084, by rfl⟩ : syracuseStep 5862779 = 8794169) B8794169
theorem B2782907 : Blo 1156638 2782907 := bstep (se 1 (by rfl) ⟨2087180, by rfl⟩ : syracuseStep 2782907 = 4174361) B4174361
theorem B2258695 : Blo 1156638 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B20051873 : Blo 1156638 20051873 := bstep (se 2 (by rfl) ⟨7519452, by rfl⟩ : syracuseStep 20051873 = 15038905) B15038905
theorem B3963161 : Blo 1156638 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B1735079 : Blo 1156638 1735079 := bstep (se 1 (by rfl) ⟨1301309, by rfl⟩ : syracuseStep 1735079 = 2602619) B2602619
theorem B1735163 : Blo 1156638 1735163 := bstep (se 1 (by rfl) ⟨1301372, by rfl⟩ : syracuseStep 1735163 = 2602745) B2602745
theorem B1735289 : Blo 1156638 1735289 := bstep (se 2 (by rfl) ⟨650733, by rfl⟩ : syracuseStep 1735289 = 1301467) B1301467
theorem B5864075 : Blo 1156638 5864075 := bstep (se 1 (by rfl) ⟨4398056, by rfl⟩ : syracuseStep 5864075 = 8796113) B8796113
theorem B1735343 : Blo 1156638 1735343 := bstep (se 1 (by rfl) ⟨1301507, by rfl⟩ : syracuseStep 1735343 = 2603015) B2603015
theorem B1735391 : Blo 1156638 1735391 := bstep (se 1 (by rfl) ⟨1301543, by rfl⟩ : syracuseStep 1735391 = 2603087) B2603087
theorem B1735655 : Blo 1156638 1735655 := bstep (se 1 (by rfl) ⟨1301741, by rfl⟩ : syracuseStep 1735655 = 2603483) B2603483
theorem B1735913 : Blo 1156638 1735913 := bstep (se 2 (by rfl) ⟨650967, by rfl⟩ : syracuseStep 1735913 = 1301935) B1301935
theorem B1735967 : Blo 1156638 1735967 := bstep (se 1 (by rfl) ⟨1301975, by rfl⟩ : syracuseStep 1735967 = 2603951) B2603951
theorem B1736135 : Blo 1156638 1736135 := bstep (se 1 (by rfl) ⟨1302101, by rfl⟩ : syracuseStep 1736135 = 2604203) B2604203
theorem B1736489 : Blo 1156638 1736489 := bstep (se 2 (by rfl) ⟨651183, by rfl⟩ : syracuseStep 1736489 = 1302367) B1302367
theorem B1736495 : Blo 1156638 1736495 := bstep (se 1 (by rfl) ⟨1302371, by rfl⟩ : syracuseStep 1736495 = 2604743) B2604743
theorem B5570639 : Blo 1156638 5570639 := bstep (se 1 (by rfl) ⟨4177979, by rfl⟩ : syracuseStep 5570639 = 8355959) B8355959
theorem B1737167 : Blo 1156638 1737167 := bstep (se 1 (by rfl) ⟨1302875, by rfl⟩ : syracuseStep 1737167 = 2605751) B2605751
theorem B1737209 : Blo 1156638 1737209 := bstep (se 2 (by rfl) ⟨651453, by rfl⟩ : syracuseStep 1737209 = 1302907) B1302907
theorem B1737311 : Blo 1156638 1737311 := bstep (se 1 (by rfl) ⟨1302983, by rfl⟩ : syracuseStep 1737311 = 2605967) B2605967
theorem B2228971 : Blo 1156638 2228971 := bstep (se 1 (by rfl) ⟨1671728, by rfl⟩ : syracuseStep 2228971 = 3343457) B3343457
theorem B4227851 : Blo 1156638 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B4391891 : Blo 1156638 4391891 := bstep (se 1 (by rfl) ⟨3293918, by rfl⟩ : syracuseStep 4391891 = 6587837) B6587837
theorem B1737791 : Blo 1156638 1737791 := bstep (se 1 (by rfl) ⟨1303343, by rfl⟩ : syracuseStep 1737791 = 2606687) B2606687
theorem B1737833 : Blo 1156638 1737833 := bstep (se 2 (by rfl) ⟨651687, by rfl⟩ : syracuseStep 1737833 = 1303375) B1303375
theorem B1737935 : Blo 1156638 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B1738139 : Blo 1156638 1738139 := bstep (se 1 (by rfl) ⟨1303604, by rfl⟩ : syracuseStep 1738139 = 2607209) B2607209
theorem B4392407 : Blo 1156638 4392407 := bstep (se 1 (by rfl) ⟨3294305, by rfl⟩ : syracuseStep 4392407 = 6588611) B6588611
theorem B16713175 : Blo 1156638 16713175 := bstep (se 1 (by rfl) ⟨12534881, by rfl⟩ : syracuseStep 16713175 = 25069763) B25069763
theorem B1738361 : Blo 1156638 1738361 := bstep (se 2 (by rfl) ⟨651885, by rfl⟩ : syracuseStep 1738361 = 1303771) B1303771
theorem B1738463 : Blo 1156638 1738463 := bstep (se 1 (by rfl) ⟨1303847, by rfl⟩ : syracuseStep 1738463 = 2607695) B2607695
theorem B1738559 : Blo 1156638 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B1738727 : Blo 1156638 1738727 := bstep (se 1 (by rfl) ⟨1304045, by rfl⟩ : syracuseStep 1738727 = 2608091) B2608091
theorem B1738745 : Blo 1156638 1738745 := bstep (se 2 (by rfl) ⟨652029, by rfl⟩ : syracuseStep 1738745 = 1304059) B1304059
theorem B1738847 : Blo 1156638 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B1738907 : Blo 1156638 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B1738943 : Blo 1156638 1738943 := bstep (se 1 (by rfl) ⟨1304207, by rfl⟩ : syracuseStep 1738943 = 2608415) B2608415
theorem B17860819 : Blo 1156638 17860819 := bstep (se 1 (by rfl) ⟨13395614, by rfl⟩ : syracuseStep 17860819 = 26791229) B26791229
theorem B1738985 : Blo 1156638 1738985 := bstep (se 2 (by rfl) ⟨652119, by rfl⟩ : syracuseStep 1738985 = 1304239) B1304239
theorem B1739291 : Blo 1156638 1739291 := bstep (se 1 (by rfl) ⟨1304468, by rfl⟩ : syracuseStep 1739291 = 2608937) B2608937
theorem B1739369 : Blo 1156638 1739369 := bstep (se 2 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 1739369 = 1304527) B1304527
theorem B5868449 : Blo 1156638 5868449 := bstep (se 2 (by rfl) ⟨2200668, by rfl⟩ : syracuseStep 5868449 = 4401337) B4401337
theorem B13732901 : Blo 1156638 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B1739897 : Blo 1156638 1739897 := bstep (se 2 (by rfl) ⟨652461, by rfl⟩ : syracuseStep 1739897 = 1304923) B1304923
theorem B1674361 : Blo 1156638 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B1739999 : Blo 1156638 1739999 := bstep (se 1 (by rfl) ⟨1304999, by rfl⟩ : syracuseStep 1739999 = 2609999) B2609999
theorem B22613215 : Blo 1156638 22613215 := bstep (se 1 (by rfl) ⟨16959911, by rfl⟩ : syracuseStep 22613215 = 33919823) B33919823
theorem B1740041 : Blo 1156638 1740041 := bstep (se 2 (by rfl) ⟨652515, by rfl⟩ : syracuseStep 1740041 = 1305031) B1305031
theorem B1740143 : Blo 1156638 1740143 := bstep (se 1 (by rfl) ⟨1305107, by rfl⟩ : syracuseStep 1740143 = 2610215) B2610215
theorem B1740263 : Blo 1156638 1740263 := bstep (se 1 (by rfl) ⟨1305197, by rfl⟩ : syracuseStep 1740263 = 2610395) B2610395
theorem B1740395 : Blo 1156638 1740395 := bstep (se 1 (by rfl) ⟨1305296, by rfl⟩ : syracuseStep 1740395 = 2610593) B2610593
theorem B1740521 : Blo 1156638 1740521 := bstep (se 2 (by rfl) ⟨652695, by rfl⟩ : syracuseStep 1740521 = 1305391) B1305391
theorem B4951847 : Blo 1156638 4951847 := bstep (se 1 (by rfl) ⟨3713885, by rfl⟩ : syracuseStep 4951847 = 7427771) B7427771
theorem B1740665 : Blo 1156638 1740665 := bstep (se 2 (by rfl) ⟨652749, by rfl⟩ : syracuseStep 1740665 = 1305499) B1305499
theorem B1740767 : Blo 1156638 1740767 := bstep (se 1 (by rfl) ⟨1305575, by rfl⟩ : syracuseStep 1740767 = 2611151) B2611151
theorem B3346555 : Blo 1156638 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B7049369 : Blo 1156638 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B4952447 : Blo 1156638 4952447 := bstep (se 1 (by rfl) ⟨3714335, by rfl⟩ : syracuseStep 4952447 = 7428671) B7428671
theorem B18780659 : Blo 1156638 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B6591071 : Blo 1156638 6591071 := bstep (se 1 (by rfl) ⟨4943303, by rfl⟩ : syracuseStep 6591071 = 9886607) B9886607
theorem B122131235 : Blo 1156638 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B25433027 : Blo 1156638 25433027 := bstep (se 1 (by rfl) ⟨19074770, by rfl⟩ : syracuseStep 25433027 = 38149541) B38149541
theorem B57119759 : Blo 1156638 57119759 := bstep (se 1 (by rfl) ⟨42839819, by rfl⟩ : syracuseStep 57119759 = 85679639) B85679639
theorem B6591527 : Blo 1156638 6591527 := bstep (se 1 (by rfl) ⟨4943645, by rfl⟩ : syracuseStep 6591527 = 9887291) B9887291
theorem B5870879 : Blo 1156638 5870879 := bstep (se 1 (by rfl) ⟨4403159, by rfl⟩ : syracuseStep 5870879 = 8806319) B8806319
theorem B3904955 : Blo 1156638 3904955 := bstep (se 1 (by rfl) ⟨2928716, by rfl⟩ : syracuseStep 3904955 = 5857433) B5857433
theorem B3905495 : Blo 1156638 3905495 := bstep (se 1 (by rfl) ⟨2929121, by rfl⟩ : syracuseStep 3905495 = 5858243) B5858243
theorem B11147345 : Blo 1156638 11147345 := bstep (se 2 (by rfl) ⟨4180254, by rfl⟩ : syracuseStep 11147345 = 8360509) B8360509
theorem B4233313 : Blo 1156638 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B2201755 : Blo 1156638 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B6592711 : Blo 1156638 6592711 := bstep (se 1 (by rfl) ⟨4944533, by rfl⟩ : syracuseStep 6592711 = 9889067) B9889067
theorem B6691019 : Blo 1156638 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B14096681 : Blo 1156638 14096681 := bstep (se 2 (by rfl) ⟨5286255, by rfl⟩ : syracuseStep 14096681 = 10572511) B10572511
theorem B5282171 : Blo 1156638 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B4397435 : Blo 1156638 4397435 := bstep (se 1 (by rfl) ⟨3298076, by rfl⟩ : syracuseStep 4397435 = 6596153) B6596153
theorem B3905981 : Blo 1156638 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B10558289 : Blo 1156638 10558289 := bstep (se 2 (by rfl) ⟨3959358, by rfl⟩ : syracuseStep 10558289 = 7918717) B7918717
theorem B50044027 : Blo 1156638 50044027 := bstep (se 1 (by rfl) ⟨37533020, by rfl⟩ : syracuseStep 50044027 = 75066041) B75066041
theorem B3906845 : Blo 1156638 3906845 := bstep (se 3 (by rfl) ⟨732533, by rfl⟩ : syracuseStep 3906845 = 1465067) B1465067
theorem B8789309 : Blo 1156638 8789309 := bstep (se 3 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 8789309 = 3295991) B3295991
theorem B6594695 : Blo 1156638 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B3907871 : Blo 1156638 3907871 := bstep (se 1 (by rfl) ⟨2930903, by rfl⟩ : syracuseStep 3907871 = 5861807) B5861807
theorem B1319375 : Blo 1156638 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B1810895 : Blo 1156638 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B5874443 : Blo 1156638 5874443 := bstep (se 1 (by rfl) ⟨4405832, by rfl⟩ : syracuseStep 5874443 = 8811665) B8811665
theorem B3908519 : Blo 1156638 3908519 := bstep (se 1 (by rfl) ⟨2931389, by rfl⟩ : syracuseStep 3908519 = 5862779) B5862779
theorem B5874605 : Blo 1156638 5874605 := bstep (se 3 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 5874605 = 2202977) B2202977
theorem B4400153 : Blo 1156638 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B25044157 : Blo 1156638 25044157 := bstep (se 3 (by rfl) ⟨4695779, by rfl⟩ : syracuseStep 25044157 = 9391559) B9391559
theorem B3909113 : Blo 1156638 3909113 := bstep (se 2 (by rfl) ⟨1465917, by rfl⟩ : syracuseStep 3909113 = 2931835) B2931835
theorem B1156719 : Blo 1156638 1156719 := bstep (se 1 (by rfl) ⟨867539, by rfl⟩ : syracuseStep 1156719 = 1735079) B1735079
theorem B1156775 : Blo 1156638 1156775 := bstep (se 1 (by rfl) ⟨867581, by rfl⟩ : syracuseStep 1156775 = 1735163) B1735163
theorem B8791739 : Blo 1156638 8791739 := bstep (se 1 (by rfl) ⟨6593804, by rfl⟩ : syracuseStep 8791739 = 13187609) B13187609
theorem B1156859 : Blo 1156638 1156859 := bstep (se 1 (by rfl) ⟨867644, by rfl⟩ : syracuseStep 1156859 = 1735289) B1735289
theorem B3909383 : Blo 1156638 3909383 := bstep (se 1 (by rfl) ⟨2932037, by rfl⟩ : syracuseStep 3909383 = 5864075) B5864075
theorem B1156895 : Blo 1156638 1156895 := bstep (se 1 (by rfl) ⟨867671, by rfl⟩ : syracuseStep 1156895 = 1735343) B1735343
theorem B3909437 : Blo 1156638 3909437 := bstep (se 3 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 3909437 = 1466039) B1466039
theorem B1156927 : Blo 1156638 1156927 := bstep (se 1 (by rfl) ⟨867695, by rfl⟩ : syracuseStep 1156927 = 1735391) B1735391
theorem B1157103 : Blo 1156638 1157103 := bstep (se 1 (by rfl) ⟨867827, by rfl⟩ : syracuseStep 1157103 = 1735655) B1735655
theorem B16721939 : Blo 1156638 16721939 := bstep (se 1 (by rfl) ⟨12541454, by rfl⟩ : syracuseStep 16721939 = 25082909) B25082909
theorem B1157275 : Blo 1156638 1157275 := bstep (se 1 (by rfl) ⟨867956, by rfl⟩ : syracuseStep 1157275 = 1735913) B1735913
theorem B1157311 : Blo 1156638 1157311 := bstep (se 1 (by rfl) ⟨867983, by rfl⟩ : syracuseStep 1157311 = 1735967) B1735967
theorem B1648873 : Blo 1156638 1648873 := bstep (se 2 (by rfl) ⟨618327, by rfl⟩ : syracuseStep 1648873 = 1236655) B1236655
theorem B1157423 : Blo 1156638 1157423 := bstep (se 1 (by rfl) ⟨868067, by rfl⟩ : syracuseStep 1157423 = 1736135) B1736135
theorem B1157659 : Blo 1156638 1157659 := bstep (se 1 (by rfl) ⟨868244, by rfl⟩ : syracuseStep 1157659 = 1736489) B1736489
theorem B1157663 : Blo 1156638 1157663 := bstep (se 1 (by rfl) ⟨868247, by rfl⟩ : syracuseStep 1157663 = 1736495) B1736495
theorem B1157979 : Blo 1156638 1157979 := bstep (se 1 (by rfl) ⟨868484, by rfl⟩ : syracuseStep 1157979 = 1736969) B1736969
theorem B1158047 : Blo 1156638 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B6597611 : Blo 1156638 6597611 := bstep (se 1 (by rfl) ⟨4948208, by rfl⟩ : syracuseStep 6597611 = 9896417) B9896417
theorem B1158191 : Blo 1156638 1158191 := bstep (se 1 (by rfl) ⟨868643, by rfl⟩ : syracuseStep 1158191 = 1737287) B1737287
theorem B1158215 : Blo 1156638 1158215 := bstep (se 1 (by rfl) ⟨868661, by rfl⟩ : syracuseStep 1158215 = 1737323) B1737323
theorem B1158367 : Blo 1156638 1158367 := bstep (se 1 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 1158367 = 1737551) B1737551
theorem B2927897 : Blo 1156638 2927897 := bstep (se 2 (by rfl) ⟨1097961, by rfl⟩ : syracuseStep 2927897 = 2195923) B2195923
theorem B1158631 : Blo 1156638 1158631 := bstep (se 1 (by rfl) ⟨868973, by rfl⟩ : syracuseStep 1158631 = 1737947) B1737947
theorem B1158747 : Blo 1156638 1158747 := bstep (se 1 (by rfl) ⟨869060, by rfl⟩ : syracuseStep 1158747 = 1738121) B1738121
theorem B21114665 : Blo 1156638 21114665 := bstep (se 2 (by rfl) ⟨7917999, by rfl⟩ : syracuseStep 21114665 = 15835999) B15835999
theorem B1158983 : Blo 1156638 1158983 := bstep (se 1 (by rfl) ⟨869237, by rfl⟩ : syracuseStep 1158983 = 1738475) B1738475
theorem B4403099 : Blo 1156638 4403099 := bstep (se 1 (by rfl) ⟨3302324, by rfl⟩ : syracuseStep 4403099 = 6604649) B6604649
theorem B1159135 : Blo 1156638 1159135 := bstep (se 1 (by rfl) ⟨869351, by rfl⟩ : syracuseStep 1159135 = 1738703) B1738703
theorem B3911867 : Blo 1156638 3911867 := bstep (se 1 (by rfl) ⟨2933900, by rfl⟩ : syracuseStep 3911867 = 5867801) B5867801
theorem B1159399 : Blo 1156638 1159399 := bstep (se 1 (by rfl) ⟨869549, by rfl⟩ : syracuseStep 1159399 = 1739099) B1739099
theorem B1978679 : Blo 1156638 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B1159551 : Blo 1156638 1159551 := bstep (se 1 (by rfl) ⟨869663, by rfl⟩ : syracuseStep 1159551 = 1739327) B1739327
theorem B1159631 : Blo 1156638 1159631 := bstep (se 1 (by rfl) ⟨869723, by rfl⟩ : syracuseStep 1159631 = 1739447) B1739447
theorem B1651151 : Blo 1156638 1651151 := bstep (se 1 (by rfl) ⟨1238363, by rfl⟩ : syracuseStep 1651151 = 2476727) B2476727
theorem B3715679 : Blo 1156638 3715679 := bstep (se 1 (by rfl) ⟨2786759, by rfl⟩ : syracuseStep 3715679 = 5573519) B5573519
theorem B67613285 : Blo 1156638 67613285 := bstep (se 4 (by rfl) ⟨6338745, by rfl⟩ : syracuseStep 67613285 = 12677491) B12677491
theorem B1159783 : Blo 1156638 1159783 := bstep (se 1 (by rfl) ⟨869837, by rfl⟩ : syracuseStep 1159783 = 1739675) B1739675
theorem B3912353 : Blo 1156638 3912353 := bstep (se 2 (by rfl) ⟨1467132, by rfl⟩ : syracuseStep 3912353 = 2934265) B2934265
theorem B1160047 : Blo 1156638 1160047 := bstep (se 1 (by rfl) ⟨870035, by rfl⟩ : syracuseStep 1160047 = 1740071) B1740071
theorem B7418749 : Blo 1156638 7418749 := bstep (se 3 (by rfl) ⟨1391015, by rfl⟩ : syracuseStep 7418749 = 2782031) B2782031
theorem B1160103 : Blo 1156638 1160103 := bstep (se 1 (by rfl) ⟨870077, by rfl⟩ : syracuseStep 1160103 = 1740155) B1740155
theorem B1160187 : Blo 1156638 1160187 := bstep (se 1 (by rfl) ⟨870140, by rfl⟩ : syracuseStep 1160187 = 1740281) B1740281
theorem B1160255 : Blo 1156638 1160255 := bstep (se 1 (by rfl) ⟨870191, by rfl⟩ : syracuseStep 1160255 = 1740383) B1740383
theorem B6599819 : Blo 1156638 6599819 := bstep (se 1 (by rfl) ⟨4949864, by rfl⟩ : syracuseStep 6599819 = 9899729) B9899729
theorem B1160399 : Blo 1156638 1160399 := bstep (se 1 (by rfl) ⟨870299, by rfl⟩ : syracuseStep 1160399 = 1740599) B1740599
theorem B2471123 : Blo 1156638 2471123 := bstep (se 1 (by rfl) ⟨1853342, by rfl⟩ : syracuseStep 2471123 = 3706685) B3706685
theorem B10040699 : Blo 1156638 10040699 := bstep (se 1 (by rfl) ⟨7530524, by rfl⟩ : syracuseStep 10040699 = 15061049) B15061049
theorem B1160603 : Blo 1156638 1160603 := bstep (se 1 (by rfl) ⟨870452, by rfl⟩ : syracuseStep 1160603 = 1740905) B1740905
theorem B3913217 : Blo 1156638 3913217 := bstep (se 2 (by rfl) ⟨1467456, by rfl⟩ : syracuseStep 3913217 = 2934913) B2934913
theorem B2602889 : Blo 1156638 2602889 := bstep (se 2 (by rfl) ⟨976083, by rfl⟩ : syracuseStep 2602889 = 1952167) B1952167
theorem B2930651 : Blo 1156638 2930651 := bstep (se 1 (by rfl) ⟨2197988, by rfl⟩ : syracuseStep 2930651 = 4395977) B4395977
theorem B4405211 : Blo 1156638 4405211 := bstep (se 1 (by rfl) ⟨3303908, by rfl⟩ : syracuseStep 4405211 = 6607817) B6607817
theorem B3913703 : Blo 1156638 3913703 := bstep (se 1 (by rfl) ⟨2935277, by rfl⟩ : syracuseStep 3913703 = 5870555) B5870555
theorem B3717103 : Blo 1156638 3717103 := bstep (se 1 (by rfl) ⟨2787827, by rfl⟩ : syracuseStep 3717103 = 5575655) B5575655
theorem B2930681 : Blo 1156638 2930681 := bstep (se 2 (by rfl) ⟨1099005, by rfl⟩ : syracuseStep 2930681 = 2198011) B2198011
theorem B3913811 : Blo 1156638 3913811 := bstep (se 1 (by rfl) ⟨2935358, by rfl⟩ : syracuseStep 3913811 = 5870717) B5870717
theorem B2603105 : Blo 1156638 2603105 := bstep (se 2 (by rfl) ⟨976164, by rfl⟩ : syracuseStep 2603105 = 1952329) B1952329
theorem B2930843 : Blo 1156638 2930843 := bstep (se 1 (by rfl) ⟨2198132, by rfl⟩ : syracuseStep 2930843 = 4396265) B4396265
theorem B1882409 : Blo 1156638 1882409 := bstep (se 2 (by rfl) ⟨705903, by rfl⟩ : syracuseStep 1882409 = 1411807) B1411807
theorem B3914027 : Blo 1156638 3914027 := bstep (se 1 (by rfl) ⟨2935520, by rfl⟩ : syracuseStep 3914027 = 5871041) B5871041
theorem B3717551 : Blo 1156638 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B3914297 : Blo 1156638 3914297 := bstep (se 2 (by rfl) ⟨1467861, by rfl⟩ : syracuseStep 3914297 = 2935723) B2935723
theorem B4012891 : Blo 1156638 4012891 := bstep (se 1 (by rfl) ⟨3009668, by rfl⟩ : syracuseStep 4012891 = 6019337) B6019337
theorem B3521789 : Blo 1156638 3521789 := bstep (se 3 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 3521789 = 1320671) B1320671
theorem B2931977 : Blo 1156638 2931977 := bstep (se 2 (by rfl) ⟨1099491, by rfl⟩ : syracuseStep 2931977 = 2198983) B2198983
theorem B2604455 : Blo 1156638 2604455 := bstep (se 1 (by rfl) ⟨1953341, by rfl⟩ : syracuseStep 2604455 = 3906683) B3906683
theorem B47037995 : Blo 1156638 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B4177487 : Blo 1156638 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B2604635 : Blo 1156638 2604635 := bstep (se 1 (by rfl) ⟨1953476, by rfl⟩ : syracuseStep 2604635 = 3906953) B3906953
theorem B2604923 : Blo 1156638 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B20070433 : Blo 1156638 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B3915809 : Blo 1156638 3915809 := bstep (se 2 (by rfl) ⟨1468428, by rfl⟩ : syracuseStep 3915809 = 2936857) B2936857
theorem B2113823 : Blo 1156638 2113823 := bstep (se 1 (by rfl) ⟨1585367, by rfl⟩ : syracuseStep 2113823 = 3170735) B3170735
theorem B2605409 : Blo 1156638 2605409 := bstep (se 2 (by rfl) ⟨977028, by rfl⟩ : syracuseStep 2605409 = 1954057) B1954057
theorem B63324517 : Blo 1156638 63324517 := bstep (se 4 (by rfl) ⟨5936673, by rfl⟩ : syracuseStep 63324517 = 11873347) B11873347
theorem B6603191 : Blo 1156638 6603191 := bstep (se 1 (by rfl) ⟨4952393, by rfl⟩ : syracuseStep 6603191 = 9904787) B9904787
theorem B2605499 : Blo 1156638 2605499 := bstep (se 1 (by rfl) ⟨1954124, by rfl⟩ : syracuseStep 2605499 = 3908249) B3908249
theorem B3293759 : Blo 1156638 3293759 := bstep (se 1 (by rfl) ⟨2470319, by rfl⟩ : syracuseStep 3293759 = 4940639) B4940639
theorem B14107927 : Blo 1156638 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B53495113 : Blo 1156638 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B6604193 : Blo 1156638 6604193 := bstep (se 2 (by rfl) ⟨2476572, by rfl⟩ : syracuseStep 6604193 = 4953145) B4953145
theorem B2606507 : Blo 1156638 2606507 := bstep (se 1 (by rfl) ⟨1954880, by rfl⟩ : syracuseStep 2606507 = 3909761) B3909761
theorem B6342239 : Blo 1156638 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B6342259 : Blo 1156638 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B3524257 : Blo 1156638 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B2606759 : Blo 1156638 2606759 := bstep (se 1 (by rfl) ⟨1955069, by rfl⟩ : syracuseStep 2606759 = 3910139) B3910139
theorem B1984223 : Blo 1156638 1984223 := bstep (se 1 (by rfl) ⟨1488167, by rfl⟩ : syracuseStep 1984223 = 2976335) B2976335
theorem B2607047 : Blo 1156638 2607047 := bstep (se 1 (by rfl) ⟨1955285, by rfl⟩ : syracuseStep 2607047 = 3910571) B3910571
theorem B2607353 : Blo 1156638 2607353 := bstep (se 2 (by rfl) ⟨977757, by rfl⟩ : syracuseStep 2607353 = 1955515) B1955515
theorem B1952039 : Blo 1156638 1952039 := bstep (se 1 (by rfl) ⟨1464029, by rfl⟩ : syracuseStep 1952039 = 2928059) B2928059
theorem B2607407 : Blo 1156638 2607407 := bstep (se 1 (by rfl) ⟨1955555, by rfl⟩ : syracuseStep 2607407 = 3911111) B3911111
theorem B2607623 : Blo 1156638 2607623 := bstep (se 1 (by rfl) ⟨1955717, by rfl⟩ : syracuseStep 2607623 = 3911435) B3911435
theorem B2607803 : Blo 1156638 2607803 := bstep (se 1 (by rfl) ⟨1955852, by rfl⟩ : syracuseStep 2607803 = 3911705) B3911705
theorem B1952815 : Blo 1156638 1952815 := bstep (se 1 (by rfl) ⟨1464611, by rfl⟩ : syracuseStep 1952815 = 2929223) B2929223
theorem B1953193 : Blo 1156638 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B2608631 : Blo 1156638 2608631 := bstep (se 1 (by rfl) ⟨1956473, by rfl⟩ : syracuseStep 2608631 = 3912947) B3912947
theorem B8474107 : Blo 1156638 8474107 := bstep (se 1 (by rfl) ⟨6355580, by rfl⟩ : syracuseStep 8474107 = 12711161) B12711161
theorem B2608703 : Blo 1156638 2608703 := bstep (se 1 (by rfl) ⟨1956527, by rfl⟩ : syracuseStep 2608703 = 3913055) B3913055
theorem B3526301 : Blo 1156638 3526301 := bstep (se 3 (by rfl) ⟨661181, by rfl⟩ : syracuseStep 3526301 = 1322363) B1322363
theorem B1855271 : Blo 1156638 1855271 := bstep (se 1 (by rfl) ⟨1391453, by rfl⟩ : syracuseStep 1855271 = 2782907) B2782907
theorem B1953659 : Blo 1156638 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B12046373 : Blo 1156638 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B2642107 : Blo 1156638 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B2937019 : Blo 1156638 2937019 := bstep (se 1 (by rfl) ⟨2202764, by rfl⟩ : syracuseStep 2937019 = 4405529) B4405529
theorem B2609657 : Blo 1156638 2609657 := bstep (se 2 (by rfl) ⟨978621, by rfl⟩ : syracuseStep 2609657 = 1957243) B1957243
theorem B2609747 : Blo 1156638 2609747 := bstep (se 1 (by rfl) ⟨1957310, by rfl⟩ : syracuseStep 2609747 = 3914621) B3914621
theorem B2937505 : Blo 1156638 2937505 := bstep (se 2 (by rfl) ⟨1101564, by rfl⟩ : syracuseStep 2937505 = 2203129) B2203129
theorem B2609927 : Blo 1156638 2609927 := bstep (se 1 (by rfl) ⟨1957445, by rfl⟩ : syracuseStep 2609927 = 3914891) B3914891
theorem B14865281 : Blo 1156638 14865281 := bstep (se 2 (by rfl) ⟨5574480, by rfl⟩ : syracuseStep 14865281 = 11148961) B11148961
theorem B3527675 : Blo 1156638 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B15258631 : Blo 1156638 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B1954921 : Blo 1156638 1954921 := bstep (se 2 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 1954921 = 1466191) B1466191
theorem B3298657 : Blo 1156638 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B37574027 : Blo 1156638 37574027 := bstep (se 1 (by rfl) ⟨28180520, by rfl⟩ : syracuseStep 37574027 = 56361041) B56361041
theorem B3298715 : Blo 1156638 3298715 := bstep (se 1 (by rfl) ⟨2474036, by rfl⟩ : syracuseStep 3298715 = 4948073) B4948073
theorem B28530299 : Blo 1156638 28530299 := bstep (se 1 (by rfl) ⟨21397724, by rfl⟩ : syracuseStep 28530299 = 42795449) B42795449
theorem B1955495 : Blo 1156638 1955495 := bstep (se 1 (by rfl) ⟨1466621, by rfl⟩ : syracuseStep 1955495 = 2933243) B2933243
theorem B1464095 : Blo 1156638 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B2611007 : Blo 1156638 2611007 := bstep (se 1 (by rfl) ⟨1958255, by rfl⟩ : syracuseStep 2611007 = 3916511) B3916511
theorem B16701299 : Blo 1156638 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B14112643 : Blo 1156638 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B2611295 : Blo 1156638 2611295 := bstep (se 1 (by rfl) ⟨1958471, by rfl⟩ : syracuseStep 2611295 = 3916943) B3916943
theorem B1464475 : Blo 1156638 1464475 := bstep (se 1 (by rfl) ⟨1098356, by rfl⟩ : syracuseStep 1464475 = 2196713) B2196713
theorem B3299591 : Blo 1156638 3299591 := bstep (se 1 (by rfl) ⟨2474693, by rfl⟩ : syracuseStep 3299591 = 4949387) B4949387
theorem B1956143 : Blo 1156638 1956143 := bstep (se 1 (by rfl) ⟨1467107, by rfl⟩ : syracuseStep 1956143 = 2934215) B2934215
theorem B6609275 : Blo 1156638 6609275 := bstep (se 1 (by rfl) ⟨4956956, by rfl⟩ : syracuseStep 6609275 = 9913913) B9913913
theorem B3299773 : Blo 1156638 3299773 := bstep (se 3 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 3299773 = 1237415) B1237415
theorem B15850009 : Blo 1156638 15850009 := bstep (se 2 (by rfl) ⟨5943753, by rfl⟩ : syracuseStep 15850009 = 11887507) B11887507
theorem B1956379 : Blo 1156638 1956379 := bstep (se 1 (by rfl) ⟨1467284, by rfl⟩ : syracuseStep 1956379 = 2934569) B2934569
theorem B6609707 : Blo 1156638 6609707 := bstep (se 1 (by rfl) ⟨4957280, by rfl⟩ : syracuseStep 6609707 = 9914561) B9914561
theorem B42326833 : Blo 1156638 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B11131739 : Blo 1156638 11131739 := bstep (se 1 (by rfl) ⟨8348804, by rfl⟩ : syracuseStep 11131739 = 16697609) B16697609
theorem B1465391 : Blo 1156638 1465391 := bstep (se 1 (by rfl) ⟨1099043, by rfl⟩ : syracuseStep 1465391 = 2198087) B2198087
theorem B1301575 : Blo 1156638 1301575 := bstep (se 1 (by rfl) ⟨976181, by rfl⟩ : syracuseStep 1301575 = 1952363) B1952363
theorem B5856623 : Blo 1156638 5856623 := bstep (se 1 (by rfl) ⟨4392467, by rfl⟩ : syracuseStep 5856623 = 8784935) B8784935
theorem B9395585 : Blo 1156638 9395585 := bstep (se 2 (by rfl) ⟨3523344, by rfl⟩ : syracuseStep 9395585 = 7046689) B7046689
theorem B67788251 : Blo 1156638 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B1957351 : Blo 1156638 1957351 := bstep (se 1 (by rfl) ⟨1468013, by rfl⟩ : syracuseStep 1957351 = 2936027) B2936027
theorem B1957439 : Blo 1156638 1957439 := bstep (se 1 (by rfl) ⟨1468079, by rfl⟩ : syracuseStep 1957439 = 2936159) B2936159
theorem B3301175 : Blo 1156638 3301175 := bstep (se 1 (by rfl) ⟨2475881, by rfl⟩ : syracuseStep 3301175 = 4951763) B4951763
theorem B1564537 : Blo 1156638 1564537 := bstep (se 2 (by rfl) ⟨586701, by rfl⟩ : syracuseStep 1564537 = 1173403) B1173403
theorem B63364999 : Blo 1156638 63364999 := bstep (se 1 (by rfl) ⟨47523749, by rfl⟩ : syracuseStep 63364999 = 95047499) B95047499
theorem B1958107 : Blo 1156638 1958107 := bstep (se 1 (by rfl) ⟨1468580, by rfl⟩ : syracuseStep 1958107 = 2937161) B2937161
theorem B1958377 : Blo 1156638 1958377 := bstep (se 2 (by rfl) ⟨734391, by rfl⟩ : syracuseStep 1958377 = 1468783) B1468783
theorem B9888317 : Blo 1156638 9888317 := bstep (se 3 (by rfl) ⟨1854059, by rfl⟩ : syracuseStep 9888317 = 3708119) B3708119
theorem B14869277 : Blo 1156638 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B28959947 : Blo 1156638 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B5564123 : Blo 1156638 5564123 := bstep (se 1 (by rfl) ⟨4173092, by rfl⟩ : syracuseStep 5564123 = 8346185) B8346185
theorem B14870303 : Blo 1156638 14870303 := bstep (se 1 (by rfl) ⟨11152727, by rfl⟩ : syracuseStep 14870303 = 22305455) B22305455
theorem B1304383 : Blo 1156638 1304383 := bstep (se 1 (by rfl) ⟨978287, by rfl⟩ : syracuseStep 1304383 = 1956575) B1956575
theorem B1304671 : Blo 1156638 1304671 := bstep (se 1 (by rfl) ⟨978503, by rfl⟩ : syracuseStep 1304671 = 1957007) B1957007
theorem B3303737 : Blo 1156638 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B43379003 : Blo 1156638 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B64286327 : Blo 1156638 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B7434433 : Blo 1156638 7434433 := bstep (se 2 (by rfl) ⟨2787912, by rfl⟩ : syracuseStep 7434433 = 5575825) B5575825
theorem B5861969 : Blo 1156638 5861969 := bstep (se 2 (by rfl) ⟨2198238, by rfl⟩ : syracuseStep 5861969 = 4396477) B4396477
theorem B12515471 : Blo 1156638 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B1734959 : Blo 1156638 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B1735199 : Blo 1156638 1735199 := bstep (se 1 (by rfl) ⟨1301399, by rfl⟩ : syracuseStep 1735199 = 2602799) B2602799
theorem B2783801 : Blo 1156638 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B13367915 : Blo 1156638 13367915 := bstep (se 1 (by rfl) ⟨10025936, by rfl⟩ : syracuseStep 13367915 = 20051873) B20051873
theorem B32143979 : Blo 1156638 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B1735583 : Blo 1156638 1735583 := bstep (se 1 (by rfl) ⟨1301687, by rfl⟩ : syracuseStep 1735583 = 2603375) B2603375
theorem B1735631 : Blo 1156638 1735631 := bstep (se 1 (by rfl) ⟨1301723, by rfl⟩ : syracuseStep 1735631 = 2603447) B2603447
theorem B5864399 : Blo 1156638 5864399 := bstep (se 1 (by rfl) ⟨4398299, by rfl⟩ : syracuseStep 5864399 = 8796599) B8796599
theorem B1735721 : Blo 1156638 1735721 := bstep (se 2 (by rfl) ⟨650895, by rfl⟩ : syracuseStep 1735721 = 1301791) B1301791
theorem B1735727 : Blo 1156638 1735727 := bstep (se 1 (by rfl) ⟨1301795, by rfl⟩ : syracuseStep 1735727 = 2603591) B2603591
theorem B1735751 : Blo 1156638 1735751 := bstep (se 1 (by rfl) ⟨1301813, by rfl⟩ : syracuseStep 1735751 = 2603627) B2603627
theorem B1736015 : Blo 1156638 1736015 := bstep (se 1 (by rfl) ⟨1302011, by rfl⟩ : syracuseStep 1736015 = 2604023) B2604023
theorem B1736105 : Blo 1156638 1736105 := bstep (se 2 (by rfl) ⟨651039, by rfl⟩ : syracuseStep 1736105 = 1302079) B1302079
theorem B1736255 : Blo 1156638 1736255 := bstep (se 1 (by rfl) ⟨1302191, by rfl⟩ : syracuseStep 1736255 = 2604383) B2604383
theorem B1736519 : Blo 1156638 1736519 := bstep (se 1 (by rfl) ⟨1302389, by rfl⟩ : syracuseStep 1736519 = 2604779) B2604779
theorem B1671035 : Blo 1156638 1671035 := bstep (se 1 (by rfl) ⟨1253276, by rfl⟩ : syracuseStep 1671035 = 2506553) B2506553
theorem B1736603 : Blo 1156638 1736603 := bstep (se 1 (by rfl) ⟨1302452, by rfl⟩ : syracuseStep 1736603 = 2604905) B2604905
theorem B1409215 : Blo 1156638 1409215 := bstep (se 1 (by rfl) ⟨1056911, by rfl⟩ : syracuseStep 1409215 = 2113823) B2113823
theorem B1736939 : Blo 1156638 1736939 := bstep (se 1 (by rfl) ⟨1302704, by rfl⟩ : syracuseStep 1736939 = 2605409) B2605409
theorem B1736999 : Blo 1156638 1736999 := bstep (se 1 (by rfl) ⟨1302749, by rfl⟩ : syracuseStep 1736999 = 2605499) B2605499
theorem B2195839 : Blo 1156638 2195839 := bstep (se 1 (by rfl) ⟨1646879, by rfl⟩ : syracuseStep 2195839 = 3293759) B3293759
theorem B2818567 : Blo 1156638 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B5276477 : Blo 1156638 5276477 := bstep (se 3 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 5276477 = 1978679) B1978679
theorem B1737671 : Blo 1156638 1737671 := bstep (se 1 (by rfl) ⟨1303253, by rfl⟩ : syracuseStep 1737671 = 2606507) B2606507
theorem B4228159 : Blo 1156638 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B1737839 : Blo 1156638 1737839 := bstep (se 1 (by rfl) ⟨1303379, by rfl⟩ : syracuseStep 1737839 = 2606759) B2606759
theorem B1738031 : Blo 1156638 1738031 := bstep (se 1 (by rfl) ⟨1303523, by rfl⟩ : syracuseStep 1738031 = 2607047) B2607047
theorem B1738235 : Blo 1156638 1738235 := bstep (se 1 (by rfl) ⟨1303676, by rfl⟩ : syracuseStep 1738235 = 2607353) B2607353
theorem B1738271 : Blo 1156638 1738271 := bstep (se 1 (by rfl) ⟨1303703, by rfl⟩ : syracuseStep 1738271 = 2607407) B2607407
theorem B33392209 : Blo 1156638 33392209 := bstep (se 2 (by rfl) ⟨12522078, by rfl⟩ : syracuseStep 33392209 = 25044157) B25044157
theorem B1738415 : Blo 1156638 1738415 := bstep (se 1 (by rfl) ⟨1303811, by rfl⟩ : syracuseStep 1738415 = 2607623) B2607623
theorem B18810569 : Blo 1156638 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B1738535 : Blo 1156638 1738535 := bstep (se 1 (by rfl) ⟨1303901, by rfl⟩ : syracuseStep 1738535 = 2607803) B2607803
theorem B22284233 : Blo 1156638 22284233 := bstep (se 2 (by rfl) ⟨8356587, by rfl⟩ : syracuseStep 22284233 = 16713175) B16713175
theorem B8456345 : Blo 1156638 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B1739087 : Blo 1156638 1739087 := bstep (se 1 (by rfl) ⟨1304315, by rfl⟩ : syracuseStep 1739087 = 2608631) B2608631
theorem B1739135 : Blo 1156638 1739135 := bstep (se 1 (by rfl) ⟨1304351, by rfl⟩ : syracuseStep 1739135 = 2608703) B2608703
theorem B1739177 : Blo 1156638 1739177 := bstep (se 2 (by rfl) ⟨652191, by rfl⟩ : syracuseStep 1739177 = 1304383) B1304383
theorem B8030915 : Blo 1156638 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B1739561 : Blo 1156638 1739561 := bstep (se 2 (by rfl) ⟨652335, by rfl⟩ : syracuseStep 1739561 = 1304671) B1304671
theorem B2198497 : Blo 1156638 2198497 := bstep (se 2 (by rfl) ⟨824436, by rfl⟩ : syracuseStep 2198497 = 1648873) B1648873
theorem B12520439 : Blo 1156638 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B1739771 : Blo 1156638 1739771 := bstep (se 1 (by rfl) ⟨1304828, by rfl⟩ : syracuseStep 1739771 = 2609657) B2609657
theorem B1739831 : Blo 1156638 1739831 := bstep (se 1 (by rfl) ⟨1304873, by rfl⟩ : syracuseStep 1739831 = 2609747) B2609747
theorem B4394047 : Blo 1156638 4394047 := bstep (se 1 (by rfl) ⟨3295535, by rfl⟩ : syracuseStep 4394047 = 6591071) B6591071
theorem B1739951 : Blo 1156638 1739951 := bstep (se 1 (by rfl) ⟨1304963, by rfl⟩ : syracuseStep 1739951 = 2609927) B2609927
theorem B38079839 : Blo 1156638 38079839 := bstep (se 1 (by rfl) ⟨28559879, by rfl⟩ : syracuseStep 38079839 = 57119759) B57119759
theorem B4394351 : Blo 1156638 4394351 := bstep (se 1 (by rfl) ⟨3295763, by rfl⟩ : syracuseStep 4394351 = 6591527) B6591527
theorem B2199143 : Blo 1156638 2199143 := bstep (se 1 (by rfl) ⟨1649357, by rfl⟩ : syracuseStep 2199143 = 3298715) B3298715
theorem B1740671 : Blo 1156638 1740671 := bstep (se 1 (by rfl) ⟨1305503, by rfl⟩ : syracuseStep 1740671 = 2611007) B2611007
theorem B1740863 : Blo 1156638 1740863 := bstep (se 1 (by rfl) ⟨1305647, by rfl⟩ : syracuseStep 1740863 = 2611295) B2611295
theorem B2232481 : Blo 1156638 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B2199727 : Blo 1156638 2199727 := bstep (se 1 (by rfl) ⟨1649795, by rfl⟩ : syracuseStep 2199727 = 3299591) B3299591
theorem B30150953 : Blo 1156638 30150953 := bstep (se 2 (by rfl) ⟨11306607, by rfl⟩ : syracuseStep 30150953 = 22613215) B22613215
theorem B21402085 : Blo 1156638 21402085 := bstep (se 4 (by rfl) ⟨2006445, by rfl⟩ : syracuseStep 21402085 = 4012891) B4012891
theorem B3904253 : Blo 1156638 3904253 := bstep (se 3 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 3904253 = 1464095) B1464095
theorem B3904415 : Blo 1156638 3904415 := bstep (se 1 (by rfl) ⟨2928311, by rfl⟩ : syracuseStep 3904415 = 5856623) B5856623
theorem B6263723 : Blo 1156638 6263723 := bstep (se 1 (by rfl) ⟨4697792, by rfl⟩ : syracuseStep 6263723 = 9395585) B9395585
theorem B45192167 : Blo 1156638 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B2200783 : Blo 1156638 2200783 := bstep (se 1 (by rfl) ⟨1650587, by rfl⟩ : syracuseStep 2200783 = 3301175) B3301175
theorem B4396463 : Blo 1156638 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B4462073 : Blo 1156638 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B6592211 : Blo 1156638 6592211 := bstep (se 1 (by rfl) ⟨4944158, by rfl⟩ : syracuseStep 6592211 = 9888317) B9888317
theorem B19306631 : Blo 1156638 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B115677341 : Blo 1156638 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B3709415 : Blo 1156638 3709415 := bstep (se 1 (by rfl) ⟨2782061, by rfl⟩ : syracuseStep 3709415 = 5564123) B5564123
theorem B11147959 : Blo 1156638 11147959 := bstep (se 1 (by rfl) ⟨8360969, by rfl⟩ : syracuseStep 11147959 = 16721939) B16721939
theorem B2202491 : Blo 1156638 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B4398209 : Blo 1156638 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B4398407 : Blo 1156638 4398407 := bstep (se 1 (by rfl) ⟨3298805, by rfl⟩ : syracuseStep 4398407 = 6597611) B6597611
theorem B18816857 : Blo 1156638 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B4956137 : Blo 1156638 4956137 := bstep (se 2 (by rfl) ⟨1858551, by rfl⟩ : syracuseStep 4956137 = 3717103) B3717103
theorem B3907709 : Blo 1156638 3907709 := bstep (se 3 (by rfl) ⟨732695, by rfl⟩ : syracuseStep 3907709 = 1465391) B1465391
theorem B5644417 : Blo 1156638 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B8790281 : Blo 1156638 8790281 := bstep (se 2 (by rfl) ⟨3296355, by rfl⟩ : syracuseStep 8790281 = 6592711) B6592711
theorem B3907979 : Blo 1156638 3907979 := bstep (se 1 (by rfl) ⟨2930984, by rfl⟩ : syracuseStep 3907979 = 5861969) B5861969
theorem B4399697 : Blo 1156638 4399697 := bstep (se 2 (by rfl) ⟨1649886, by rfl⟩ : syracuseStep 4399697 = 3299773) B3299773
theorem B4399879 : Blo 1156638 4399879 := bstep (se 1 (by rfl) ⟨3299909, by rfl⟩ : syracuseStep 4399879 = 6599819) B6599819
theorem B1647415 : Blo 1156638 1647415 := bstep (se 1 (by rfl) ⟨1235561, by rfl⟩ : syracuseStep 1647415 = 2471123) B2471123
theorem B6693799 : Blo 1156638 6693799 := bstep (se 1 (by rfl) ⟨5020349, by rfl⟩ : syracuseStep 6693799 = 10040699) B10040699
theorem B56435777 : Blo 1156638 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B66725369 : Blo 1156638 66725369 := bstep (se 2 (by rfl) ⟨25022013, by rfl⟩ : syracuseStep 66725369 = 50044027) B50044027
theorem B1156639 : Blo 1156638 1156639 := bstep (se 1 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 1156639 = 1734959) B1734959
theorem B1156799 : Blo 1156638 1156799 := bstep (se 1 (by rfl) ⟨867599, by rfl⟩ : syracuseStep 1156799 = 1735199) B1735199
theorem B1157055 : Blo 1156638 1157055 := bstep (se 1 (by rfl) ⟨867791, by rfl⟩ : syracuseStep 1157055 = 1735583) B1735583
theorem B1157087 : Blo 1156638 1157087 := bstep (se 1 (by rfl) ⟨867815, by rfl⟩ : syracuseStep 1157087 = 1735631) B1735631
theorem B3909599 : Blo 1156638 3909599 := bstep (se 1 (by rfl) ⟨2932199, by rfl⟩ : syracuseStep 3909599 = 5864399) B5864399
theorem B1157147 : Blo 1156638 1157147 := bstep (se 1 (by rfl) ⟨867860, by rfl⟩ : syracuseStep 1157147 = 1735721) B1735721
theorem B1157151 : Blo 1156638 1157151 := bstep (se 1 (by rfl) ⟨867863, by rfl⟩ : syracuseStep 1157151 = 1735727) B1735727
theorem B1157167 : Blo 1156638 1157167 := bstep (se 1 (by rfl) ⟨867875, by rfl⟩ : syracuseStep 1157167 = 1735751) B1735751
theorem B1157343 : Blo 1156638 1157343 := bstep (se 1 (by rfl) ⟨868007, by rfl⟩ : syracuseStep 1157343 = 1736015) B1736015
theorem B1157403 : Blo 1156638 1157403 := bstep (se 1 (by rfl) ⟨868052, by rfl⟩ : syracuseStep 1157403 = 1736105) B1736105
theorem B1157503 : Blo 1156638 1157503 := bstep (se 1 (by rfl) ⟨868127, by rfl⟩ : syracuseStep 1157503 = 1736255) B1736255
theorem B84486665 : Blo 1156638 84486665 := bstep (se 2 (by rfl) ⟨31682499, by rfl⟩ : syracuseStep 84486665 = 63364999) B63364999
theorem B1157679 : Blo 1156638 1157679 := bstep (se 1 (by rfl) ⟨868259, by rfl⟩ : syracuseStep 1157679 = 1736519) B1736519
theorem B1157735 : Blo 1156638 1157735 := bstep (se 1 (by rfl) ⟨868301, by rfl⟩ : syracuseStep 1157735 = 1736603) B1736603
theorem B3713759 : Blo 1156638 3713759 := bstep (se 1 (by rfl) ⟨2785319, by rfl⟩ : syracuseStep 3713759 = 5570639) B5570639
theorem B4402127 : Blo 1156638 4402127 := bstep (se 1 (by rfl) ⟨3301595, by rfl⟩ : syracuseStep 4402127 = 6603191) B6603191
theorem B1158111 : Blo 1156638 1158111 := bstep (se 1 (by rfl) ⟨868583, by rfl⟩ : syracuseStep 1158111 = 1737167) B1737167
theorem B1158139 : Blo 1156638 1158139 := bstep (se 1 (by rfl) ⟨868604, by rfl⟩ : syracuseStep 1158139 = 1737209) B1737209
theorem B1158207 : Blo 1156638 1158207 := bstep (se 1 (by rfl) ⟨868655, by rfl⟩ : syracuseStep 1158207 = 1737311) B1737311
theorem B2927927 : Blo 1156638 2927927 := bstep (se 1 (by rfl) ⟨2195945, by rfl⟩ : syracuseStep 2927927 = 4391891) B4391891
theorem B1158527 : Blo 1156638 1158527 := bstep (se 1 (by rfl) ⟨868895, by rfl⟩ : syracuseStep 1158527 = 1737791) B1737791
theorem B1158555 : Blo 1156638 1158555 := bstep (se 1 (by rfl) ⟨868916, by rfl⟩ : syracuseStep 1158555 = 1737833) B1737833
theorem B1158623 : Blo 1156638 1158623 := bstep (se 1 (by rfl) ⟨868967, by rfl⟩ : syracuseStep 1158623 = 1737935) B1737935
theorem B1158759 : Blo 1156638 1158759 := bstep (se 1 (by rfl) ⟨869069, by rfl⟩ : syracuseStep 1158759 = 1738139) B1738139
theorem B4402795 : Blo 1156638 4402795 := bstep (se 1 (by rfl) ⟨3302096, by rfl⟩ : syracuseStep 4402795 = 6604193) B6604193
theorem B2928271 : Blo 1156638 2928271 := bstep (se 1 (by rfl) ⟨2196203, by rfl⟩ : syracuseStep 2928271 = 4392407) B4392407
theorem B1158907 : Blo 1156638 1158907 := bstep (se 1 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 1158907 = 1738361) B1738361
theorem B1158975 : Blo 1156638 1158975 := bstep (se 1 (by rfl) ⟨869231, by rfl⟩ : syracuseStep 1158975 = 1738463) B1738463
theorem B1322815 : Blo 1156638 1322815 := bstep (se 1 (by rfl) ⟨992111, by rfl⟩ : syracuseStep 1322815 = 1984223) B1984223
theorem B3518333 : Blo 1156638 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B4829053 : Blo 1156638 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B1159039 : Blo 1156638 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B4403069 : Blo 1156638 4403069 := bstep (se 3 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 4403069 = 1651151) B1651151
theorem B1159151 : Blo 1156638 1159151 := bstep (se 1 (by rfl) ⟨869363, by rfl⟩ : syracuseStep 1159151 = 1738727) B1738727
theorem B1159163 : Blo 1156638 1159163 := bstep (se 1 (by rfl) ⟨869372, by rfl⟩ : syracuseStep 1159163 = 1738745) B1738745
theorem B1159231 : Blo 1156638 1159231 := bstep (se 1 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 1159231 = 1738847) B1738847
theorem B1159271 : Blo 1156638 1159271 := bstep (se 1 (by rfl) ⟨869453, by rfl⟩ : syracuseStep 1159271 = 1738907) B1738907
theorem B1159295 : Blo 1156638 1159295 := bstep (se 1 (by rfl) ⟨869471, by rfl⟩ : syracuseStep 1159295 = 1738943) B1738943
theorem B1159323 : Blo 1156638 1159323 := bstep (se 1 (by rfl) ⟨869492, by rfl⟩ : syracuseStep 1159323 = 1738985) B1738985
theorem B9908477 : Blo 1156638 9908477 := bstep (se 3 (by rfl) ⟨1857839, by rfl⟩ : syracuseStep 9908477 = 3715679) B3715679
theorem B1159527 : Blo 1156638 1159527 := bstep (se 1 (by rfl) ⟨869645, by rfl⟩ : syracuseStep 1159527 = 1739291) B1739291
theorem B1159579 : Blo 1156638 1159579 := bstep (se 1 (by rfl) ⟨869684, by rfl⟩ : syracuseStep 1159579 = 1739369) B1739369
theorem B3912299 : Blo 1156638 3912299 := bstep (se 1 (by rfl) ⟨2934224, by rfl⟩ : syracuseStep 3912299 = 5868449) B5868449
theorem B9155267 : Blo 1156638 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B1159931 : Blo 1156638 1159931 := bstep (se 1 (by rfl) ⟨869948, by rfl⟩ : syracuseStep 1159931 = 1739897) B1739897
theorem B1159999 : Blo 1156638 1159999 := bstep (se 1 (by rfl) ⟨869999, by rfl⟩ : syracuseStep 1159999 = 1739999) B1739999
theorem B1160027 : Blo 1156638 1160027 := bstep (se 1 (by rfl) ⟨870020, by rfl⟩ : syracuseStep 1160027 = 1740041) B1740041
theorem B4699009 : Blo 1156638 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B1160095 : Blo 1156638 1160095 := bstep (se 1 (by rfl) ⟨870071, by rfl⟩ : syracuseStep 1160095 = 1740143) B1740143
theorem B1160175 : Blo 1156638 1160175 := bstep (se 1 (by rfl) ⟨870131, by rfl⟩ : syracuseStep 1160175 = 1740263) B1740263
theorem B1160263 : Blo 1156638 1160263 := bstep (se 1 (by rfl) ⟨870197, by rfl⟩ : syracuseStep 1160263 = 1740395) B1740395
theorem B1160347 : Blo 1156638 1160347 := bstep (se 1 (by rfl) ⟨870260, by rfl⟩ : syracuseStep 1160347 = 1740521) B1740521
theorem B1160443 : Blo 1156638 1160443 := bstep (se 1 (by rfl) ⟨870332, by rfl⟩ : syracuseStep 1160443 = 1740665) B1740665
theorem B1160511 : Blo 1156638 1160511 := bstep (se 1 (by rfl) ⟨870383, by rfl⟩ : syracuseStep 1160511 = 1740767) B1740767
theorem B4699579 : Blo 1156638 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B9910187 : Blo 1156638 9910187 := bstep (se 1 (by rfl) ⟨7432640, by rfl⟩ : syracuseStep 9910187 = 14865281) B14865281
theorem B16955351 : Blo 1156638 16955351 := bstep (se 1 (by rfl) ⟨12716513, by rfl⟩ : syracuseStep 16955351 = 25433027) B25433027
theorem B3913919 : Blo 1156638 3913919 := bstep (se 1 (by rfl) ⟨2935439, by rfl⟩ : syracuseStep 3913919 = 5870879) B5870879
theorem B25049351 : Blo 1156638 25049351 := bstep (se 1 (by rfl) ⟨18787013, by rfl⟩ : syracuseStep 25049351 = 37574027) B37574027
theorem B2603303 : Blo 1156638 2603303 := bstep (se 1 (by rfl) ⟨1952477, by rfl⟩ : syracuseStep 2603303 = 3904955) B3904955
theorem B19020199 : Blo 1156638 19020199 := bstep (se 1 (by rfl) ⟨14265149, by rfl⟩ : syracuseStep 19020199 = 28530299) B28530299
theorem B2603663 : Blo 1156638 2603663 := bstep (se 1 (by rfl) ⟨1952747, by rfl⟩ : syracuseStep 2603663 = 3905495) B3905495
theorem B2603753 : Blo 1156638 2603753 := bstep (se 2 (by rfl) ⟨976407, by rfl⟩ : syracuseStep 2603753 = 1952815) B1952815
theorem B3521447 : Blo 1156638 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B2931623 : Blo 1156638 2931623 := bstep (se 1 (by rfl) ⟨2198717, by rfl⟩ : syracuseStep 2931623 = 4397435) B4397435
theorem B4406183 : Blo 1156638 4406183 := bstep (se 1 (by rfl) ⟨3304637, by rfl⟩ : syracuseStep 4406183 = 6609275) B6609275
theorem B2603987 : Blo 1156638 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B4406471 : Blo 1156638 4406471 := bstep (se 1 (by rfl) ⟨3304853, by rfl⟩ : syracuseStep 4406471 = 6609707) B6609707
theorem B2604257 : Blo 1156638 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B7421159 : Blo 1156638 7421159 := bstep (se 1 (by rfl) ⟨5565869, by rfl⟩ : syracuseStep 7421159 = 11131739) B11131739
theorem B2604563 : Blo 1156638 2604563 := bstep (se 1 (by rfl) ⟨1953422, by rfl⟩ : syracuseStep 2604563 = 3906845) B3906845
theorem B2605247 : Blo 1156638 2605247 := bstep (se 1 (by rfl) ⟨1953935, by rfl⟩ : syracuseStep 2605247 = 3907871) B3907871
theorem B3522809 : Blo 1156638 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B3916025 : Blo 1156638 3916025 := bstep (se 2 (by rfl) ⟨1468509, by rfl⟩ : syracuseStep 3916025 = 2937019) B2937019
theorem B9912577 : Blo 1156638 9912577 := bstep (se 2 (by rfl) ⟨3717216, by rfl⟩ : syracuseStep 9912577 = 7434433) B7434433
theorem B3916295 : Blo 1156638 3916295 := bstep (se 1 (by rfl) ⟨2937221, by rfl⟩ : syracuseStep 3916295 = 5874443) B5874443
theorem B9912851 : Blo 1156638 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B17842717 : Blo 1156638 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B2605679 : Blo 1156638 2605679 := bstep (se 1 (by rfl) ⟨1954259, by rfl⟩ : syracuseStep 2605679 = 3908519) B3908519
theorem B3916403 : Blo 1156638 3916403 := bstep (se 1 (by rfl) ⟨2937302, by rfl⟩ : syracuseStep 3916403 = 5874605) B5874605
theorem B2933435 : Blo 1156638 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B3916673 : Blo 1156638 3916673 := bstep (se 2 (by rfl) ⟨1468752, by rfl⟩ : syracuseStep 3916673 = 2937505) B2937505
theorem B2606075 : Blo 1156638 2606075 := bstep (se 1 (by rfl) ⟨1954556, by rfl⟩ : syracuseStep 2606075 = 3909113) B3909113
theorem B2606255 : Blo 1156638 2606255 := bstep (se 1 (by rfl) ⟨1954691, by rfl⟩ : syracuseStep 2606255 = 3909383) B3909383
theorem B9913535 : Blo 1156638 9913535 := bstep (se 1 (by rfl) ⟨7435151, by rfl⟩ : syracuseStep 9913535 = 14870303) B14870303
theorem B2606291 : Blo 1156638 2606291 := bstep (se 1 (by rfl) ⟨1954718, by rfl⟩ : syracuseStep 2606291 = 3909437) B3909437
theorem B2606561 : Blo 1156638 2606561 := bstep (se 2 (by rfl) ⟨977460, by rfl⟩ : syracuseStep 2606561 = 1954921) B1954921
theorem B1951931 : Blo 1156638 1951931 := bstep (se 1 (by rfl) ⟨1463948, by rfl⟩ : syracuseStep 1951931 = 2927897) B2927897
theorem B14076443 : Blo 1156638 14076443 := bstep (se 1 (by rfl) ⟨10557332, by rfl⟩ : syracuseStep 14076443 = 21114665) B21114665
theorem B2935399 : Blo 1156638 2935399 := bstep (se 1 (by rfl) ⟨2201549, by rfl⟩ : syracuseStep 2935399 = 4403099) B4403099
theorem B2607911 : Blo 1156638 2607911 := bstep (se 1 (by rfl) ⟨1955933, by rfl⟩ : syracuseStep 2607911 = 3911867) B3911867
theorem B1952633 : Blo 1156638 1952633 := bstep (se 2 (by rfl) ⟨732237, by rfl⟩ : syracuseStep 1952633 = 1464475) B1464475
theorem B2935673 : Blo 1156638 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B45075523 : Blo 1156638 45075523 := bstep (se 1 (by rfl) ⟨33806642, by rfl⟩ : syracuseStep 45075523 = 67613285) B67613285
theorem B2608235 : Blo 1156638 2608235 := bstep (se 1 (by rfl) ⟨1956176, by rfl⟩ : syracuseStep 2608235 = 3912353) B3912353
theorem B2608505 : Blo 1156638 2608505 := bstep (se 2 (by rfl) ⟨978189, by rfl⟩ : syracuseStep 2608505 = 1956379) B1956379
theorem B2608811 : Blo 1156638 2608811 := bstep (se 1 (by rfl) ⟨1956608, by rfl⟩ : syracuseStep 2608811 = 3913217) B3913217
theorem B1953767 : Blo 1156638 1953767 := bstep (se 1 (by rfl) ⟨1465325, by rfl⟩ : syracuseStep 1953767 = 2930651) B2930651
theorem B2936807 : Blo 1156638 2936807 := bstep (se 1 (by rfl) ⟨2202605, by rfl⟩ : syracuseStep 2936807 = 4405211) B4405211
theorem B2609135 : Blo 1156638 2609135 := bstep (se 1 (by rfl) ⟨1956851, by rfl⟩ : syracuseStep 2609135 = 3913703) B3913703
theorem B1953787 : Blo 1156638 1953787 := bstep (se 1 (by rfl) ⟨1465340, by rfl⟩ : syracuseStep 1953787 = 2930681) B2930681
theorem B2609207 : Blo 1156638 2609207 := bstep (se 1 (by rfl) ⟨1956905, by rfl⟩ : syracuseStep 2609207 = 3913811) B3913811
theorem B8343647 : Blo 1156638 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B1953895 : Blo 1156638 1953895 := bstep (se 1 (by rfl) ⟨1465421, by rfl⟩ : syracuseStep 1953895 = 2930843) B2930843
theorem B2609351 : Blo 1156638 2609351 := bstep (se 1 (by rfl) ⟨1957013, by rfl⟩ : syracuseStep 2609351 = 3914027) B3914027
theorem B2478367 : Blo 1156638 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B1855867 : Blo 1156638 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B2609531 : Blo 1156638 2609531 := bstep (se 1 (by rfl) ⟨1957148, by rfl⟩ : syracuseStep 2609531 = 3914297) B3914297
theorem B2609801 : Blo 1156638 2609801 := bstep (se 2 (by rfl) ⟨978675, by rfl⟩ : syracuseStep 2609801 = 1957351) B1957351
theorem B2347859 : Blo 1156638 2347859 := bstep (se 1 (by rfl) ⟨1760894, by rfl⟩ : syracuseStep 2347859 = 3521789) B3521789
theorem B1954651 : Blo 1156638 1954651 := bstep (se 1 (by rfl) ⟨1465988, by rfl⟩ : syracuseStep 1954651 = 2931977) B2931977
theorem B2086049 : Blo 1156638 2086049 := bstep (se 2 (by rfl) ⟨782268, by rfl⟩ : syracuseStep 2086049 = 1564537) B1564537
theorem B2610539 : Blo 1156638 2610539 := bstep (se 1 (by rfl) ⟨1957904, by rfl⟩ : syracuseStep 2610539 = 3915809) B3915809
theorem B26760577 : Blo 1156638 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B2610809 : Blo 1156638 2610809 := bstep (se 2 (by rfl) ⟨979053, by rfl⟩ : syracuseStep 2610809 = 1958107) B1958107
theorem B84432689 : Blo 1156638 84432689 := bstep (se 2 (by rfl) ⟨31662258, by rfl⟩ : syracuseStep 84432689 = 63324517) B63324517
theorem B2611169 : Blo 1156638 2611169 := bstep (se 2 (by rfl) ⟨979188, by rfl⟩ : syracuseStep 2611169 = 1958377) B1958377
theorem B2971961 : Blo 1156638 2971961 := bstep (se 2 (by rfl) ⟨1114485, by rfl⟩ : syracuseStep 2971961 = 2228971) B2228971
theorem B1301359 : Blo 1156638 1301359 := bstep (se 1 (by rfl) ⟨976019, by rfl⟩ : syracuseStep 1301359 = 1952039) B1952039
theorem B71326817 : Blo 1156638 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B3301231 : Blo 1156638 3301231 := bstep (se 1 (by rfl) ⟨2475923, by rfl⟩ : syracuseStep 3301231 = 4951847) B4951847
theorem B1302439 : Blo 1156638 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B84533381 : Blo 1156638 84533381 := bstep (se 4 (by rfl) ⟨7925004, by rfl⟩ : syracuseStep 84533381 = 15850009) B15850009
theorem B3301631 : Blo 1156638 3301631 := bstep (se 1 (by rfl) ⟨2476223, by rfl⟩ : syracuseStep 3301631 = 4952447) B4952447
theorem B23814425 : Blo 1156638 23814425 := bstep (se 2 (by rfl) ⟨8930409, by rfl⟩ : syracuseStep 23814425 = 17860819) B17860819
theorem B20079029 : Blo 1156638 20079029 := bstep (se 5 (by rfl) ⟨941204, by rfl⟩ : syracuseStep 20079029 = 1882409) B1882409
theorem B81420823 : Blo 1156638 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B2351783 : Blo 1156638 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1303663 : Blo 1156638 1303663 := bstep (se 1 (by rfl) ⟨977747, by rfl⟩ : syracuseStep 1303663 = 1955495) B1955495
theorem B11134199 : Blo 1156638 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B7431563 : Blo 1156638 7431563 := bstep (se 1 (by rfl) ⟨5573672, by rfl⟩ : syracuseStep 7431563 = 11147345) B11147345
theorem B9397787 : Blo 1156638 9397787 := bstep (se 1 (by rfl) ⟨7048340, by rfl⟩ : syracuseStep 9397787 = 14096681) B14096681
theorem B1304095 : Blo 1156638 1304095 := bstep (se 1 (by rfl) ⟨978071, by rfl⟩ : syracuseStep 1304095 = 1956143) B1956143
theorem B7038859 : Blo 1156638 7038859 := bstep (se 1 (by rfl) ⟨5279144, by rfl⟩ : syracuseStep 7038859 = 10558289) B10558289
theorem B11298809 : Blo 1156638 11298809 := bstep (se 2 (by rfl) ⟨4237053, by rfl⟩ : syracuseStep 11298809 = 8474107) B8474107
theorem B5859539 : Blo 1156638 5859539 := bstep (se 1 (by rfl) ⟨4394654, by rfl⟩ : syracuseStep 5859539 = 8789309) B8789309
theorem B1304959 : Blo 1156638 1304959 := bstep (se 1 (by rfl) ⟨978719, by rfl⟩ : syracuseStep 1304959 = 1957439) B1957439
theorem B5861159 : Blo 1156638 5861159 := bstep (se 1 (by rfl) ⟨4395869, by rfl⟩ : syracuseStep 5861159 = 8791739) B8791739
theorem B9891665 : Blo 1156638 9891665 := bstep (se 2 (by rfl) ⟨3709374, by rfl⟩ : syracuseStep 9891665 = 7418749) B7418749
theorem B20344841 : Blo 1156638 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B42857551 : Blo 1156638 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B1735259 : Blo 1156638 1735259 := bstep (se 1 (by rfl) ⟨1301444, by rfl⟩ : syracuseStep 1735259 = 2602889) B2602889
theorem B1735403 : Blo 1156638 1735403 := bstep (se 1 (by rfl) ⟨1301552, by rfl⟩ : syracuseStep 1735403 = 2603105) B2603105
theorem B1735433 : Blo 1156638 1735433 := bstep (se 2 (by rfl) ⟨650787, by rfl⟩ : syracuseStep 1735433 = 1301575) B1301575
theorem B8911943 : Blo 1156638 8911943 := bstep (se 1 (by rfl) ⟨6683957, by rfl⟩ : syracuseStep 8911943 = 13367915) B13367915
theorem B21429319 : Blo 1156638 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B9403469 : Blo 1156638 9403469 := bstep (se 3 (by rfl) ⟨1763150, by rfl⟩ : syracuseStep 9403469 = 3526301) B3526301
theorem B4947389 : Blo 1156638 4947389 := bstep (se 3 (by rfl) ⟨927635, by rfl⟩ : syracuseStep 4947389 = 1855271) B1855271
theorem B1736303 : Blo 1156638 1736303 := bstep (se 1 (by rfl) ⟨1302227, by rfl⟩ : syracuseStep 1736303 = 2604455) B2604455
theorem B4456093 : Blo 1156638 4456093 := bstep (se 3 (by rfl) ⟨835517, by rfl⟩ : syracuseStep 4456093 = 1671035) B1671035
theorem B31358663 : Blo 1156638 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B2784991 : Blo 1156638 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B1736423 : Blo 1156638 1736423 := bstep (se 1 (by rfl) ⟨1302317, by rfl⟩ : syracuseStep 1736423 = 2604635) B2604635
theorem B1736615 : Blo 1156638 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B1736831 : Blo 1156638 1736831 := bstep (se 1 (by rfl) ⟨1302623, by rfl⟩ : syracuseStep 1736831 = 2605247) B2605247
theorem B1737119 : Blo 1156638 1737119 := bstep (se 1 (by rfl) ⟨1302839, by rfl⟩ : syracuseStep 1737119 = 2605679) B2605679
theorem B1737383 : Blo 1156638 1737383 := bstep (se 1 (by rfl) ⟨1303037, by rfl⟩ : syracuseStep 1737383 = 2606075) B2606075
theorem B108561097 : Blo 1156638 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B23790289 : Blo 1156638 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B1737503 : Blo 1156638 1737503 := bstep (se 1 (by rfl) ⟨1303127, by rfl⟩ : syracuseStep 1737503 = 2606255) B2606255
theorem B1737527 : Blo 1156638 1737527 := bstep (se 1 (by rfl) ⟨1303145, by rfl⟩ : syracuseStep 1737527 = 2606291) B2606291
theorem B1737707 : Blo 1156638 1737707 := bstep (se 1 (by rfl) ⟨1303280, by rfl⟩ : syracuseStep 1737707 = 2606561) B2606561
theorem B5866505 : Blo 1156638 5866505 := bstep (se 2 (by rfl) ⟨2199939, by rfl⟩ : syracuseStep 5866505 = 4399879) B4399879
theorem B2196553 : Blo 1156638 2196553 := bstep (se 2 (by rfl) ⟨823707, by rfl⟩ : syracuseStep 2196553 = 1647415) B1647415
theorem B5637545 : Blo 1156638 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B5637563 : Blo 1156638 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B1738217 : Blo 1156638 1738217 := bstep (se 2 (by rfl) ⟨651831, by rfl⟩ : syracuseStep 1738217 = 1303663) B1303663
theorem B1738607 : Blo 1156638 1738607 := bstep (se 1 (by rfl) ⟨1303955, by rfl⟩ : syracuseStep 1738607 = 2607911) B2607911
theorem B1738793 : Blo 1156638 1738793 := bstep (se 2 (by rfl) ⟨652047, by rfl⟩ : syracuseStep 1738793 = 1304095) B1304095
theorem B1738823 : Blo 1156638 1738823 := bstep (se 1 (by rfl) ⟨1304117, by rfl⟩ : syracuseStep 1738823 = 2608235) B2608235
theorem B1739003 : Blo 1156638 1739003 := bstep (se 1 (by rfl) ⟨1304252, by rfl⟩ : syracuseStep 1739003 = 2608505) B2608505
theorem B1739207 : Blo 1156638 1739207 := bstep (se 1 (by rfl) ⟨1304405, by rfl⟩ : syracuseStep 1739207 = 2608811) B2608811
theorem B1739423 : Blo 1156638 1739423 := bstep (se 1 (by rfl) ⟨1304567, by rfl⟩ : syracuseStep 1739423 = 2609135) B2609135
theorem B1739471 : Blo 1156638 1739471 := bstep (se 1 (by rfl) ⟨1304603, by rfl⟩ : syracuseStep 1739471 = 2609207) B2609207
theorem B1739567 : Blo 1156638 1739567 := bstep (se 1 (by rfl) ⟨1304675, by rfl⟩ : syracuseStep 1739567 = 2609351) B2609351
theorem B1739687 : Blo 1156638 1739687 := bstep (se 1 (by rfl) ⟨1304765, by rfl⟩ : syracuseStep 1739687 = 2609531) B2609531
theorem B1739867 : Blo 1156638 1739867 := bstep (se 1 (by rfl) ⟨1304900, by rfl⟩ : syracuseStep 1739867 = 2609801) B2609801
theorem B1739945 : Blo 1156638 1739945 := bstep (se 2 (by rfl) ⟨652479, by rfl⟩ : syracuseStep 1739945 = 1304959) B1304959
theorem B1740359 : Blo 1156638 1740359 := bstep (se 1 (by rfl) ⟨1305269, by rfl⟩ : syracuseStep 1740359 = 2610539) B2610539
theorem B1740539 : Blo 1156638 1740539 := bstep (se 1 (by rfl) ⟨1305404, by rfl⟩ : syracuseStep 1740539 = 2610809) B2610809
theorem B4394807 : Blo 1156638 4394807 := bstep (se 1 (by rfl) ⟨3296105, by rfl⟩ : syracuseStep 4394807 = 6592211) B6592211
theorem B1740779 : Blo 1156638 1740779 := bstep (se 1 (by rfl) ⟨1305584, by rfl⟩ : syracuseStep 1740779 = 2611169) B2611169
theorem B60100697 : Blo 1156638 60100697 := bstep (se 2 (by rfl) ⟨22537761, by rfl⟩ : syracuseStep 60100697 = 45075523) B45075523
theorem B47551211 : Blo 1156638 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B5870393 : Blo 1156638 5870393 := bstep (se 2 (by rfl) ⟨2201397, by rfl⟩ : syracuseStep 5870393 = 4402795) B4402795
theorem B3904361 : Blo 1156638 3904361 := bstep (se 2 (by rfl) ⟨1464135, by rfl⟩ : syracuseStep 3904361 = 2928271) B2928271
theorem B2201087 : Blo 1156638 2201087 := bstep (se 1 (by rfl) ⟨1650815, by rfl⟩ : syracuseStep 2201087 = 3301631) B3301631
theorem B51484349 : Blo 1156638 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B37623851 : Blo 1156638 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B4954375 : Blo 1156638 4954375 := bstep (se 1 (by rfl) ⟨3715781, by rfl⟩ : syracuseStep 4954375 = 7431563) B7431563
theorem B6265345 : Blo 1156638 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B3906359 : Blo 1156638 3906359 := bstep (se 1 (by rfl) ⟨2929769, by rfl⟩ : syracuseStep 3906359 = 5859539) B5859539
theorem B6266105 : Blo 1156638 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B5873309 : Blo 1156638 5873309 := bstep (se 3 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 5873309 = 2202491) B2202491
theorem B3907439 : Blo 1156638 3907439 := bstep (se 1 (by rfl) ⟨2930579, by rfl⟩ : syracuseStep 3907439 = 5861159) B5861159
theorem B6594443 : Blo 1156638 6594443 := bstep (se 1 (by rfl) ⟨4945832, by rfl⟩ : syracuseStep 6594443 = 9891665) B9891665
theorem B6103511 : Blo 1156638 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B1156839 : Blo 1156638 1156839 := bstep (se 1 (by rfl) ⟨867629, by rfl⟩ : syracuseStep 1156839 = 1735259) B1735259
theorem B1156935 : Blo 1156638 1156935 := bstep (se 1 (by rfl) ⟨867701, by rfl⟩ : syracuseStep 1156935 = 1735403) B1735403
theorem B1156955 : Blo 1156638 1156955 := bstep (se 1 (by rfl) ⟨867716, by rfl⟩ : syracuseStep 1156955 = 1735433) B1735433
theorem B5941295 : Blo 1156638 5941295 := bstep (se 1 (by rfl) ⟨4455971, by rfl⟩ : syracuseStep 5941295 = 8911943) B8911943
theorem B6268979 : Blo 1156638 6268979 := bstep (se 1 (by rfl) ⟨4701734, by rfl⟩ : syracuseStep 6268979 = 9403469) B9403469
theorem B5941457 : Blo 1156638 5941457 := bstep (se 2 (by rfl) ⟨2228046, by rfl⟩ : syracuseStep 5941457 = 4456093) B4456093
theorem B3713321 : Blo 1156638 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B1157535 : Blo 1156638 1157535 := bstep (se 1 (by rfl) ⟨868151, by rfl⟩ : syracuseStep 1157535 = 1736303) B1736303
theorem B4401641 : Blo 1156638 4401641 := bstep (se 2 (by rfl) ⟨1650615, by rfl⟩ : syracuseStep 4401641 = 3301231) B3301231
theorem B1157615 : Blo 1156638 1157615 := bstep (se 1 (by rfl) ⟨868211, by rfl⟩ : syracuseStep 1157615 = 1736423) B1736423
theorem B1157743 : Blo 1156638 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B1157959 : Blo 1156638 1157959 := bstep (se 1 (by rfl) ⟨868469, by rfl⟩ : syracuseStep 1157959 = 1736939) B1736939
theorem B1157999 : Blo 1156638 1157999 := bstep (se 1 (by rfl) ⟨868499, by rfl⟩ : syracuseStep 1157999 = 1736999) B1736999
theorem B1878953 : Blo 1156638 1878953 := bstep (se 2 (by rfl) ⟨704607, by rfl⟩ : syracuseStep 1878953 = 1409215) B1409215
theorem B13216769 : Blo 1156638 13216769 := bstep (se 2 (by rfl) ⟨4956288, by rfl⟩ : syracuseStep 13216769 = 9912577) B9912577
theorem B2927785 : Blo 1156638 2927785 := bstep (se 2 (by rfl) ⟨1097919, by rfl⟩ : syracuseStep 2927785 = 2195839) B2195839
theorem B3517651 : Blo 1156638 3517651 := bstep (se 1 (by rfl) ⟨2638238, by rfl⟩ : syracuseStep 3517651 = 5276477) B5276477
theorem B1158447 : Blo 1156638 1158447 := bstep (se 1 (by rfl) ⟨868835, by rfl⟩ : syracuseStep 1158447 = 1737671) B1737671
theorem B1158559 : Blo 1156638 1158559 := bstep (se 1 (by rfl) ⟨868919, by rfl⟩ : syracuseStep 1158559 = 1737839) B1737839
theorem B1158687 : Blo 1156638 1158687 := bstep (se 1 (by rfl) ⟨869015, by rfl⟩ : syracuseStep 1158687 = 1738031) B1738031
theorem B1158823 : Blo 1156638 1158823 := bstep (se 1 (by rfl) ⟨869117, by rfl⟩ : syracuseStep 1158823 = 1738235) B1738235
theorem B1158847 : Blo 1156638 1158847 := bstep (se 1 (by rfl) ⟨869135, by rfl⟩ : syracuseStep 1158847 = 1738271) B1738271
theorem B1158943 : Blo 1156638 1158943 := bstep (se 1 (by rfl) ⟨869207, by rfl⟩ : syracuseStep 1158943 = 1738415) B1738415
theorem B1159023 : Blo 1156638 1159023 := bstep (se 1 (by rfl) ⟨869267, by rfl⟩ : syracuseStep 1159023 = 1738535) B1738535
theorem B8925065 : Blo 1156638 8925065 := bstep (se 2 (by rfl) ⟨3346899, by rfl⟩ : syracuseStep 8925065 = 6693799) B6693799
theorem B14856155 : Blo 1156638 14856155 := bstep (se 1 (by rfl) ⟨11142116, by rfl⟩ : syracuseStep 14856155 = 22284233) B22284233
theorem B1159391 : Blo 1156638 1159391 := bstep (se 1 (by rfl) ⟨869543, by rfl⟩ : syracuseStep 1159391 = 1739087) B1739087
theorem B1159423 : Blo 1156638 1159423 := bstep (se 1 (by rfl) ⟨869567, by rfl⟩ : syracuseStep 1159423 = 1739135) B1739135
theorem B1159451 : Blo 1156638 1159451 := bstep (se 1 (by rfl) ⟨869588, by rfl⟩ : syracuseStep 1159451 = 1739177) B1739177
theorem B9384295 : Blo 1156638 9384295 := bstep (se 1 (by rfl) ⟨7038221, by rfl⟩ : syracuseStep 9384295 = 14076443) B14076443
theorem B5353943 : Blo 1156638 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B1159707 : Blo 1156638 1159707 := bstep (se 1 (by rfl) ⟨869780, by rfl⟩ : syracuseStep 1159707 = 1739561) B1739561
theorem B1159847 : Blo 1156638 1159847 := bstep (se 1 (by rfl) ⟨869885, by rfl⟩ : syracuseStep 1159847 = 1739771) B1739771
theorem B1159887 : Blo 1156638 1159887 := bstep (se 1 (by rfl) ⟨869915, by rfl⟩ : syracuseStep 1159887 = 1739831) B1739831
theorem B1159967 : Blo 1156638 1159967 := bstep (se 1 (by rfl) ⟨869975, by rfl⟩ : syracuseStep 1159967 = 1739951) B1739951
theorem B2929567 : Blo 1156638 2929567 := bstep (se 1 (by rfl) ⟨2197175, by rfl⟩ : syracuseStep 2929567 = 4394351) B4394351
theorem B9385145 : Blo 1156638 9385145 := bstep (se 2 (by rfl) ⟨3519429, by rfl⟩ : syracuseStep 9385145 = 7038859) B7038859
theorem B1160447 : Blo 1156638 1160447 := bstep (se 1 (by rfl) ⟨870335, by rfl⟩ : syracuseStep 1160447 = 1740671) B1740671
theorem B1160575 : Blo 1156638 1160575 := bstep (se 1 (by rfl) ⟨870431, by rfl⟩ : syracuseStep 1160575 = 1740863) B1740863
theorem B20100635 : Blo 1156638 20100635 := bstep (se 1 (by rfl) ⟨15075476, by rfl⟩ : syracuseStep 20100635 = 30150953) B30150953
theorem B2602835 : Blo 1156638 2602835 := bstep (se 1 (by rfl) ⟨1952126, by rfl⟩ : syracuseStep 2602835 = 3904253) B3904253
theorem B2602943 : Blo 1156638 2602943 := bstep (se 1 (by rfl) ⟨1952207, by rfl⟩ : syracuseStep 2602943 = 3904415) B3904415
theorem B4175815 : Blo 1156638 4175815 := bstep (se 1 (by rfl) ⟨3131861, by rfl⟩ : syracuseStep 4175815 = 6263723) B6263723
theorem B30128111 : Blo 1156638 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B1390699 : Blo 1156638 1390699 := bstep (se 1 (by rfl) ⟨1043024, by rfl⟩ : syracuseStep 1390699 = 2086049) B2086049
theorem B3913865 : Blo 1156638 3913865 := bstep (se 2 (by rfl) ⟨1467699, by rfl⟩ : syracuseStep 3913865 = 2935399) B2935399
theorem B2930975 : Blo 1156638 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B2931329 : Blo 1156638 2931329 := bstep (se 2 (by rfl) ⟨1099248, by rfl⟩ : syracuseStep 2931329 = 2198497) B2198497
theorem B77118227 : Blo 1156638 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B1981307 : Blo 1156638 1981307 := bstep (se 1 (by rfl) ⟨1485980, by rfl⟩ : syracuseStep 1981307 = 2971961) B2971961
theorem B2472943 : Blo 1156638 2472943 := bstep (se 1 (by rfl) ⟨1854707, by rfl⟩ : syracuseStep 2472943 = 3709415) B3709415
theorem B2932139 : Blo 1156638 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B2932271 : Blo 1156638 2932271 := bstep (se 1 (by rfl) ⟨2199203, by rfl⟩ : syracuseStep 2932271 = 4398407) B4398407
theorem B6438737 : Blo 1156638 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B30130157 : Blo 1156638 30130157 := bstep (se 3 (by rfl) ⟨5649404, by rfl⟩ : syracuseStep 30130157 = 11298809) B11298809
theorem B2605049 : Blo 1156638 2605049 := bstep (se 2 (by rfl) ⟨976893, by rfl⟩ : syracuseStep 2605049 = 1953787) B1953787
theorem B2605139 : Blo 1156638 2605139 := bstep (se 1 (by rfl) ⟨1953854, by rfl⟩ : syracuseStep 2605139 = 3907709) B3907709
theorem B2605193 : Blo 1156638 2605193 := bstep (se 2 (by rfl) ⟨976947, by rfl⟩ : syracuseStep 2605193 = 1953895) B1953895
theorem B15876283 : Blo 1156638 15876283 := bstep (se 1 (by rfl) ⟨11907212, by rfl⟩ : syracuseStep 15876283 = 23814425) B23814425
theorem B2932969 : Blo 1156638 2932969 := bstep (se 2 (by rfl) ⟨1099863, by rfl⟩ : syracuseStep 2932969 = 2199727) B2199727
theorem B2605319 : Blo 1156638 2605319 := bstep (se 1 (by rfl) ⟨1953989, by rfl⟩ : syracuseStep 2605319 = 3907979) B3907979
theorem B13386019 : Blo 1156638 13386019 := bstep (se 1 (by rfl) ⟨10039514, by rfl⟩ : syracuseStep 13386019 = 20079029) B20079029
theorem B2933131 : Blo 1156638 2933131 := bstep (se 1 (by rfl) ⟨2199848, by rfl⟩ : syracuseStep 2933131 = 4399697) B4399697
theorem B228573605 : Blo 1156638 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B2474489 : Blo 1156638 2474489 := bstep (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) B1855867
theorem B7422799 : Blo 1156638 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B44483579 : Blo 1156638 44483579 := bstep (se 1 (by rfl) ⟨33362684, by rfl⟩ : syracuseStep 44483579 = 66725369) B66725369
theorem B2606201 : Blo 1156638 2606201 := bstep (se 2 (by rfl) ⟨977325, by rfl⟩ : syracuseStep 2606201 = 1954651) B1954651
theorem B2606399 : Blo 1156638 2606399 := bstep (se 1 (by rfl) ⟨1954799, by rfl⟩ : syracuseStep 2606399 = 3909599) B3909599
theorem B2934377 : Blo 1156638 2934377 := bstep (se 2 (by rfl) ⟨1100391, by rfl⟩ : syracuseStep 2934377 = 2200783) B2200783
theorem B2475839 : Blo 1156638 2475839 := bstep (se 1 (by rfl) ⟨1856879, by rfl⟩ : syracuseStep 2475839 = 3713759) B3713759
theorem B2934751 : Blo 1156638 2934751 := bstep (se 1 (by rfl) ⟨2201063, by rfl⟩ : syracuseStep 2934751 = 4402127) B4402127
theorem B1951951 : Blo 1156638 1951951 := bstep (se 1 (by rfl) ⟨1463963, by rfl⟩ : syracuseStep 1951951 = 2927927) B2927927
theorem B2345555 : Blo 1156638 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B2935379 : Blo 1156638 2935379 := bstep (se 1 (by rfl) ⟨2201534, by rfl⟩ : syracuseStep 2935379 = 4403069) B4403069
theorem B6605651 : Blo 1156638 6605651 := bstep (se 1 (by rfl) ⟨4954238, by rfl⟩ : syracuseStep 6605651 = 9908477) B9908477
theorem B2608199 : Blo 1156638 2608199 := bstep (se 1 (by rfl) ⟨1956149, by rfl⟩ : syracuseStep 2608199 = 3912299) B3912299
theorem B14863945 : Blo 1156638 14863945 := bstep (se 2 (by rfl) ⟨5573979, by rfl⟩ : syracuseStep 14863945 = 11147959) B11147959
theorem B6606791 : Blo 1156638 6606791 := bstep (se 1 (by rfl) ⟨4955093, by rfl⟩ : syracuseStep 6606791 = 9910187) B9910187
theorem B2609279 : Blo 1156638 2609279 := bstep (se 1 (by rfl) ⟨1956959, by rfl⟩ : syracuseStep 2609279 = 3913919) B3913919
theorem B16699567 : Blo 1156638 16699567 := bstep (se 1 (by rfl) ⟨12524675, by rfl⟩ : syracuseStep 16699567 = 25049351) B25049351
theorem B2347631 : Blo 1156638 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B1954415 : Blo 1156638 1954415 := bstep (se 1 (by rfl) ⟨1465811, by rfl⟩ : syracuseStep 1954415 = 2931623) B2931623
theorem B2937455 : Blo 1156638 2937455 := bstep (se 1 (by rfl) ⟨2203091, by rfl⟩ : syracuseStep 2937455 = 4406183) B4406183
theorem B2937647 : Blo 1156638 2937647 := bstep (se 1 (by rfl) ⟨2203235, by rfl⟩ : syracuseStep 2937647 = 4406471) B4406471
theorem B3298259 : Blo 1156638 3298259 := bstep (se 1 (by rfl) ⟨2473694, by rfl⟩ : syracuseStep 3298259 = 4947389) B4947389
theorem B2610683 : Blo 1156638 2610683 := bstep (se 1 (by rfl) ⟨1958012, by rfl⟩ : syracuseStep 2610683 = 3916025) B3916025
theorem B7525889 : Blo 1156638 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B2610863 : Blo 1156638 2610863 := bstep (se 1 (by rfl) ⟨1958147, by rfl⟩ : syracuseStep 2610863 = 3916295) B3916295
theorem B6608567 : Blo 1156638 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B2610935 : Blo 1156638 2610935 := bstep (se 1 (by rfl) ⟨1958201, by rfl⟩ : syracuseStep 2610935 = 3916403) B3916403
theorem B1955623 : Blo 1156638 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B2611115 : Blo 1156638 2611115 := bstep (se 1 (by rfl) ⟨1958336, by rfl⟩ : syracuseStep 2611115 = 3916673) B3916673
theorem B9394157 : Blo 1156638 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B3758089 : Blo 1156638 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B6609023 : Blo 1156638 6609023 := bstep (se 1 (by rfl) ⟨4956767, by rfl⟩ : syracuseStep 6609023 = 9913535) B9913535
theorem B12540379 : Blo 1156638 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B1301287 : Blo 1156638 1301287 := bstep (se 1 (by rfl) ⟨975965, by rfl⟩ : syracuseStep 1301287 = 1951931) B1951931
theorem B1301755 : Blo 1156638 1301755 := bstep (se 1 (by rfl) ⟨976316, by rfl⟩ : syracuseStep 1301755 = 1952633) B1952633
theorem B1957115 : Blo 1156638 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B8346959 : Blo 1156638 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B44522945 : Blo 1156638 44522945 := bstep (se 2 (by rfl) ⟨16696104, by rfl⟩ : syracuseStep 44522945 = 33392209) B33392209
theorem B1466095 : Blo 1156638 1466095 := bstep (se 1 (by rfl) ⟨1099571, by rfl⟩ : syracuseStep 1466095 = 2199143) B2199143
theorem B1302511 : Blo 1156638 1302511 := bstep (se 1 (by rfl) ⟨976883, by rfl⟩ : syracuseStep 1302511 = 1953767) B1953767
theorem B1957871 : Blo 1156638 1957871 := bstep (se 1 (by rfl) ⟨1468403, by rfl⟩ : syracuseStep 1957871 = 2936807) B2936807
theorem B5562431 : Blo 1156638 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B1565239 : Blo 1156638 1565239 := bstep (se 1 (by rfl) ⟨1173929, by rfl⟩ : syracuseStep 1565239 = 2347859) B2347859
theorem B2974715 : Blo 1156638 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B56288459 : Blo 1156638 56288459 := bstep (se 1 (by rfl) ⟨42216344, by rfl⟩ : syracuseStep 56288459 = 84432689) B84432689
theorem B25060765 : Blo 1156638 25060765 := bstep (se 3 (by rfl) ⟨4698893, by rfl⟩ : syracuseStep 25060765 = 9397787) B9397787
theorem B5858729 : Blo 1156638 5858729 := bstep (se 2 (by rfl) ⟨2197023, by rfl⟩ : syracuseStep 5858729 = 4394047) B4394047
theorem B1763753 : Blo 1156638 1763753 := bstep (se 2 (by rfl) ⟨661407, by rfl⟩ : syracuseStep 1763753 = 1322815) B1322815
theorem B12544571 : Blo 1156638 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B3304091 : Blo 1156638 3304091 := bstep (se 1 (by rfl) ⟨2478068, by rfl⟩ : syracuseStep 3304091 = 4956137) B4956137
theorem B56355587 : Blo 1156638 56355587 := bstep (se 1 (by rfl) ⟨42266690, by rfl⟩ : syracuseStep 56355587 = 84533381) B84533381
theorem B5860187 : Blo 1156638 5860187 := bstep (se 1 (by rfl) ⟨4395140, by rfl⟩ : syracuseStep 5860187 = 8790281) B8790281
theorem B2976641 : Blo 1156638 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B3304489 : Blo 1156638 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B1567855 : Blo 1156638 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B28536113 : Blo 1156638 28536113 := bstep (se 2 (by rfl) ⟨10701042, by rfl⟩ : syracuseStep 28536113 = 21402085) B21402085
theorem B56324443 : Blo 1156638 56324443 := bstep (se 1 (by rfl) ⟨42243332, by rfl⟩ : syracuseStep 56324443 = 84486665) B84486665
theorem B35680769 : Blo 1156638 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B13563227 : Blo 1156638 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B25360265 : Blo 1156638 25360265 := bstep (se 2 (by rfl) ⟨9510099, by rfl⟩ : syracuseStep 25360265 = 19020199) B19020199
theorem B101546237 : Blo 1156638 101546237 := bstep (se 3 (by rfl) ⟨19039919, by rfl⟩ : syracuseStep 101546237 = 38079839) B38079839
theorem B1735145 : Blo 1156638 1735145 := bstep (se 2 (by rfl) ⟨650679, by rfl⟩ : syracuseStep 1735145 = 1301359) B1301359
theorem B11303567 : Blo 1156638 11303567 := bstep (se 1 (by rfl) ⟨8477675, by rfl⟩ : syracuseStep 11303567 = 16955351) B16955351
theorem B28572425 : Blo 1156638 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B1735535 : Blo 1156638 1735535 := bstep (se 1 (by rfl) ⟨1301651, by rfl⟩ : syracuseStep 1735535 = 2603303) B2603303
theorem B1735775 : Blo 1156638 1735775 := bstep (se 1 (by rfl) ⟨1301831, by rfl⟩ : syracuseStep 1735775 = 2603663) B2603663
theorem B1735835 : Blo 1156638 1735835 := bstep (se 1 (by rfl) ⟨1301876, by rfl⟩ : syracuseStep 1735835 = 2603753) B2603753
theorem B1735991 : Blo 1156638 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B1736171 : Blo 1156638 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B4947439 : Blo 1156638 4947439 := bstep (se 1 (by rfl) ⟨3710579, by rfl⟩ : syracuseStep 4947439 = 7421159) B7421159
theorem B1736375 : Blo 1156638 1736375 := bstep (se 1 (by rfl) ⟨1302281, by rfl⟩ : syracuseStep 1736375 = 2604563) B2604563
theorem B20905775 : Blo 1156638 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B1736585 : Blo 1156638 1736585 := bstep (se 2 (by rfl) ⟨651219, by rfl⟩ : syracuseStep 1736585 = 1302439) B1302439
theorem B1736759 : Blo 1156638 1736759 := bstep (se 1 (by rfl) ⟨1302569, by rfl⟩ : syracuseStep 1736759 = 2605139) B2605139
theorem B1736795 : Blo 1156638 1736795 := bstep (se 1 (by rfl) ⟨1302596, by rfl⟩ : syracuseStep 1736795 = 2605193) B2605193
theorem B1736879 : Blo 1156638 1736879 := bstep (se 1 (by rfl) ⟨1302659, by rfl⟩ : syracuseStep 1736879 = 2605319) B2605319
theorem B21168377 : Blo 1156638 21168377 := bstep (se 2 (by rfl) ⟨7938141, by rfl⟩ : syracuseStep 21168377 = 15876283) B15876283
theorem B29655719 : Blo 1156638 29655719 := bstep (se 1 (by rfl) ⟨22241789, by rfl⟩ : syracuseStep 29655719 = 44483579) B44483579
theorem B1737467 : Blo 1156638 1737467 := bstep (se 1 (by rfl) ⟨1303100, by rfl⟩ : syracuseStep 1737467 = 2606201) B2606201
theorem B1737599 : Blo 1156638 1737599 := bstep (se 1 (by rfl) ⟨1303199, by rfl⟩ : syracuseStep 1737599 = 2606399) B2606399
theorem B31720385 : Blo 1156638 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B9897065 : Blo 1156638 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B1738799 : Blo 1156638 1738799 := bstep (se 1 (by rfl) ⟨1304099, by rfl⟩ : syracuseStep 1738799 = 2608199) B2608199
theorem B1739519 : Blo 1156638 1739519 := bstep (se 1 (by rfl) ⟨1304639, by rfl⟩ : syracuseStep 1739519 = 2609279) B2609279
theorem B2198839 : Blo 1156638 2198839 := bstep (se 1 (by rfl) ⟨1649129, by rfl⟩ : syracuseStep 2198839 = 3298259) B3298259
theorem B1740455 : Blo 1156638 1740455 := bstep (se 1 (by rfl) ⟨1305341, by rfl⟩ : syracuseStep 1740455 = 2610683) B2610683
theorem B5017259 : Blo 1156638 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B1740575 : Blo 1156638 1740575 := bstep (se 1 (by rfl) ⟨1305431, by rfl⟩ : syracuseStep 1740575 = 2610863) B2610863
theorem B1740623 : Blo 1156638 1740623 := bstep (se 1 (by rfl) ⟨1305467, by rfl⟩ : syracuseStep 1740623 = 2610935) B2610935
theorem B1740743 : Blo 1156638 1740743 := bstep (se 1 (by rfl) ⟨1305557, by rfl⟩ : syracuseStep 1740743 = 2611115) B2611115
theorem B6262771 : Blo 1156638 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B3903713 : Blo 1156638 3903713 := bstep (se 2 (by rfl) ⟨1463892, by rfl⟩ : syracuseStep 3903713 = 2927785) B2927785
theorem B4396295 : Blo 1156638 4396295 := bstep (se 1 (by rfl) ⟨3297221, by rfl⟩ : syracuseStep 4396295 = 6594443) B6594443
theorem B3708287 : Blo 1156638 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B4069007 : Blo 1156638 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B8361893 : Blo 1156638 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B9902189 : Blo 1156638 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B37525639 : Blo 1156638 37525639 := bstep (se 1 (by rfl) ⟨28144229, by rfl⟩ : syracuseStep 37525639 = 56288459) B56288459
theorem B3905819 : Blo 1156638 3905819 := bstep (se 1 (by rfl) ⟨2929364, by rfl⟩ : syracuseStep 3905819 = 5858729) B5858729
theorem B3906089 : Blo 1156638 3906089 := bstep (se 2 (by rfl) ⟨1464783, by rfl⟩ : syracuseStep 3906089 = 2929567) B2929567
theorem B8363047 : Blo 1156638 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B2202727 : Blo 1156638 2202727 := bstep (se 1 (by rfl) ⟨1652045, by rfl⟩ : syracuseStep 2202727 = 3304091) B3304091
theorem B3906791 : Blo 1156638 3906791 := bstep (se 1 (by rfl) ⟨2930093, by rfl⟩ : syracuseStep 3906791 = 5860187) B5860187
theorem B9904103 : Blo 1156638 9904103 := bstep (se 1 (by rfl) ⟨7428077, by rfl⟩ : syracuseStep 9904103 = 14856155) B14856155
theorem B16720505 : Blo 1156638 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B1156763 : Blo 1156638 1156763 := bstep (se 1 (by rfl) ⟨867572, by rfl⟩ : syracuseStep 1156763 = 1735145) B1735145
theorem B19048283 : Blo 1156638 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B1157023 : Blo 1156638 1157023 := bstep (se 1 (by rfl) ⟨867767, by rfl⟩ : syracuseStep 1157023 = 1735535) B1735535
theorem B1320871 : Blo 1156638 1320871 := bstep (se 1 (by rfl) ⟨990653, by rfl⟩ : syracuseStep 1320871 = 1981307) B1981307
theorem B6596585 : Blo 1156638 6596585 := bstep (se 2 (by rfl) ⟨2473719, by rfl⟩ : syracuseStep 6596585 = 4947439) B4947439
theorem B1157183 : Blo 1156638 1157183 := bstep (se 1 (by rfl) ⟨867887, by rfl⟩ : syracuseStep 1157183 = 1735775) B1735775
theorem B1157223 : Blo 1156638 1157223 := bstep (se 1 (by rfl) ⟨867917, by rfl⟩ : syracuseStep 1157223 = 1735835) B1735835
theorem B1157327 : Blo 1156638 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B1157447 : Blo 1156638 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B1157583 : Blo 1156638 1157583 := bstep (se 1 (by rfl) ⟨868187, by rfl⟩ : syracuseStep 1157583 = 1736375) B1736375
theorem B13937183 : Blo 1156638 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B1157723 : Blo 1156638 1157723 := bstep (se 1 (by rfl) ⟨868292, by rfl⟩ : syracuseStep 1157723 = 1736585) B1736585
theorem B1157887 : Blo 1156638 1157887 := bstep (se 1 (by rfl) ⟨868415, by rfl⟩ : syracuseStep 1157887 = 1736831) B1736831
theorem B1158079 : Blo 1156638 1158079 := bstep (se 1 (by rfl) ⟨868559, by rfl⟩ : syracuseStep 1158079 = 1737119) B1737119
theorem B152382403 : Blo 1156638 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B3910625 : Blo 1156638 3910625 := bstep (se 2 (by rfl) ⟨1466484, by rfl⟩ : syracuseStep 3910625 = 2932969) B2932969
theorem B1649659 : Blo 1156638 1649659 := bstep (se 1 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 1649659 = 2474489) B2474489
theorem B1158255 : Blo 1156638 1158255 := bstep (se 1 (by rfl) ⟨868691, by rfl⟩ : syracuseStep 1158255 = 1737383) B1737383
theorem B3910841 : Blo 1156638 3910841 := bstep (se 2 (by rfl) ⟨1466565, by rfl⟩ : syracuseStep 3910841 = 2933131) B2933131
theorem B1158335 : Blo 1156638 1158335 := bstep (se 1 (by rfl) ⟨868751, by rfl⟩ : syracuseStep 1158335 = 1737503) B1737503
theorem B1158351 : Blo 1156638 1158351 := bstep (se 1 (by rfl) ⟨868763, by rfl⟩ : syracuseStep 1158351 = 1737527) B1737527
theorem B1158471 : Blo 1156638 1158471 := bstep (se 1 (by rfl) ⟨868853, by rfl⟩ : syracuseStep 1158471 = 1737707) B1737707
theorem B3911003 : Blo 1156638 3911003 := bstep (se 1 (by rfl) ⟨2933252, by rfl⟩ : syracuseStep 3911003 = 5866505) B5866505
theorem B144748129 : Blo 1156638 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B1158811 : Blo 1156638 1158811 := bstep (se 1 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 1158811 = 1738217) B1738217
theorem B1650559 : Blo 1156638 1650559 := bstep (se 1 (by rfl) ⟨1237919, by rfl⟩ : syracuseStep 1650559 = 2475839) B2475839
theorem B1159071 : Blo 1156638 1159071 := bstep (se 1 (by rfl) ⟨869303, by rfl⟩ : syracuseStep 1159071 = 1738607) B1738607
theorem B1159195 : Blo 1156638 1159195 := bstep (se 1 (by rfl) ⟨869396, by rfl⟩ : syracuseStep 1159195 = 1738793) B1738793
theorem B1159215 : Blo 1156638 1159215 := bstep (se 1 (by rfl) ⟨869411, by rfl⟩ : syracuseStep 1159215 = 1738823) B1738823
theorem B2928737 : Blo 1156638 2928737 := bstep (se 2 (by rfl) ⟨1098276, by rfl⟩ : syracuseStep 2928737 = 2196553) B2196553
theorem B1159335 : Blo 1156638 1159335 := bstep (se 1 (by rfl) ⟨869501, by rfl⟩ : syracuseStep 1159335 = 1739003) B1739003
theorem B1159471 : Blo 1156638 1159471 := bstep (se 1 (by rfl) ⟨869603, by rfl⟩ : syracuseStep 1159471 = 1739207) B1739207
theorem B1159615 : Blo 1156638 1159615 := bstep (se 1 (by rfl) ⟨869711, by rfl⟩ : syracuseStep 1159615 = 1739423) B1739423
theorem B1159647 : Blo 1156638 1159647 := bstep (se 1 (by rfl) ⟨869735, by rfl⟩ : syracuseStep 1159647 = 1739471) B1739471
theorem B1159711 : Blo 1156638 1159711 := bstep (se 1 (by rfl) ⟨869783, by rfl⟩ : syracuseStep 1159711 = 1739567) B1739567
theorem B4403767 : Blo 1156638 4403767 := bstep (se 1 (by rfl) ⟨3302825, by rfl⟩ : syracuseStep 4403767 = 6605651) B6605651
theorem B1159791 : Blo 1156638 1159791 := bstep (se 1 (by rfl) ⟨869843, by rfl⟩ : syracuseStep 1159791 = 1739687) B1739687
theorem B1159911 : Blo 1156638 1159911 := bstep (se 1 (by rfl) ⟨869933, by rfl⟩ : syracuseStep 1159911 = 1739867) B1739867
theorem B1159963 : Blo 1156638 1159963 := bstep (se 1 (by rfl) ⟨869972, by rfl⟩ : syracuseStep 1159963 = 1739945) B1739945
theorem B1160239 : Blo 1156638 1160239 := bstep (se 1 (by rfl) ⟨870179, by rfl⟩ : syracuseStep 1160239 = 1740359) B1740359
theorem B1160359 : Blo 1156638 1160359 := bstep (se 1 (by rfl) ⟨870269, by rfl⟩ : syracuseStep 1160359 = 1740539) B1740539
theorem B2929871 : Blo 1156638 2929871 := bstep (se 1 (by rfl) ⟨2197403, by rfl⟩ : syracuseStep 2929871 = 4394807) B4394807
theorem B3913001 : Blo 1156638 3913001 := bstep (se 2 (by rfl) ⟨1467375, by rfl⟩ : syracuseStep 3913001 = 2934751) B2934751
theorem B4404527 : Blo 1156638 4404527 := bstep (se 1 (by rfl) ⟨3303395, by rfl⟩ : syracuseStep 4404527 = 6606791) B6606791
theorem B1160519 : Blo 1156638 1160519 := bstep (se 1 (by rfl) ⟨870389, by rfl⟩ : syracuseStep 1160519 = 1740779) B1740779
theorem B2602601 : Blo 1156638 2602601 := bstep (se 2 (by rfl) ⟨975975, by rfl⟩ : syracuseStep 2602601 = 1951951) B1951951
theorem B31700807 : Blo 1156638 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B3913595 : Blo 1156638 3913595 := bstep (se 1 (by rfl) ⟨2935196, by rfl⟩ : syracuseStep 3913595 = 5870393) B5870393
theorem B2602907 : Blo 1156638 2602907 := bstep (se 1 (by rfl) ⟨1952180, by rfl⟩ : syracuseStep 2602907 = 3904361) B3904361
theorem B4405711 : Blo 1156638 4405711 := bstep (se 1 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 4405711 = 6608567) B6608567
theorem B34322899 : Blo 1156638 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B25082567 : Blo 1156638 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B4405985 : Blo 1156638 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B4406015 : Blo 1156638 4406015 := bstep (se 1 (by rfl) ⟨3304511, by rfl⟩ : syracuseStep 4406015 = 6609023) B6609023
theorem B2604239 : Blo 1156638 2604239 := bstep (se 1 (by rfl) ⟨1953179, by rfl⟩ : syracuseStep 2604239 = 3906359) B3906359
theorem B4177403 : Blo 1156638 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B3915539 : Blo 1156638 3915539 := bstep (se 1 (by rfl) ⟨2936654, by rfl⟩ : syracuseStep 3915539 = 5873309) B5873309
theorem B2604959 : Blo 1156638 2604959 := bstep (se 1 (by rfl) ⟨1953719, by rfl⟩ : syracuseStep 2604959 = 3907439) B3907439
theorem B22266089 : Blo 1156638 22266089 := bstep (se 2 (by rfl) ⟨8349783, by rfl⟩ : syracuseStep 22266089 = 16699567) B16699567
theorem B1983143 : Blo 1156638 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B18760805 : Blo 1156638 18760805 := bstep (se 4 (by rfl) ⟨1758825, by rfl⟩ : syracuseStep 18760805 = 3517651) B3517651
theorem B4703341 : Blo 1156638 4703341 := bstep (se 3 (by rfl) ⟨881876, by rfl⟩ : syracuseStep 4703341 = 1763753) B1763753
theorem B4179319 : Blo 1156638 4179319 := bstep (se 1 (by rfl) ⟨3134489, by rfl⟩ : syracuseStep 4179319 = 6268979) B6268979
theorem B2934427 : Blo 1156638 2934427 := bstep (se 1 (by rfl) ⟨2200820, by rfl⟩ : syracuseStep 2934427 = 4401641) B4401641
theorem B37570391 : Blo 1156638 37570391 := bstep (se 1 (by rfl) ⟨28177793, by rfl⟩ : syracuseStep 37570391 = 56355587) B56355587
theorem B1984427 : Blo 1156638 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B19024075 : Blo 1156638 19024075 := bstep (se 1 (by rfl) ⟨14268056, by rfl⟩ : syracuseStep 19024075 = 28536113) B28536113
theorem B2607497 : Blo 1156638 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B5950043 : Blo 1156638 5950043 := bstep (se 1 (by rfl) ⟨4462532, by rfl⟩ : syracuseStep 5950043 = 8925065) B8925065
theorem B1854265 : Blo 1156638 1854265 := bstep (se 2 (by rfl) ⟨695349, by rfl⟩ : syracuseStep 1854265 = 1390699) B1390699
theorem B6605833 : Blo 1156638 6605833 := bstep (se 2 (by rfl) ⟨2477187, by rfl⟩ : syracuseStep 6605833 = 4954375) B4954375
theorem B3297257 : Blo 1156638 3297257 := bstep (se 2 (by rfl) ⟨1236471, by rfl⟩ : syracuseStep 3297257 = 2472943) B2472943
theorem B2609243 : Blo 1156638 2609243 := bstep (se 1 (by rfl) ⟨1956932, by rfl⟩ : syracuseStep 2609243 = 3913865) B3913865
theorem B1953983 : Blo 1156638 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B1954219 : Blo 1156638 1954219 := bstep (se 1 (by rfl) ⟨1465664, by rfl⟩ : syracuseStep 1954219 = 2931329) B2931329
theorem B1954759 : Blo 1156638 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B1954793 : Blo 1156638 1954793 := bstep (se 2 (by rfl) ⟨733047, by rfl⟩ : syracuseStep 1954793 = 1466095) B1466095
theorem B1954847 : Blo 1156638 1954847 := bstep (se 1 (by rfl) ⟨1466135, by rfl⟩ : syracuseStep 1954847 = 2932271) B2932271
theorem B17848025 : Blo 1156638 17848025 := bstep (se 2 (by rfl) ⟨6693009, by rfl⟩ : syracuseStep 17848025 = 13386019) B13386019
theorem B2086985 : Blo 1156638 2086985 := bstep (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) B1565239
theorem B3758363 : Blo 1156638 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B3758375 : Blo 1156638 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B1956251 : Blo 1156638 1956251 := bstep (se 1 (by rfl) ⟨1467188, by rfl⟩ : syracuseStep 1956251 = 2934377) B2934377
theorem B14277181 : Blo 1156638 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B1956919 : Blo 1156638 1956919 := bstep (se 1 (by rfl) ⟨1467689, by rfl⟩ : syracuseStep 1956919 = 2935379) B2935379
theorem B33414353 : Blo 1156638 33414353 := bstep (se 2 (by rfl) ⟨12530382, by rfl⟩ : syracuseStep 33414353 = 25060765) B25060765
theorem B40067131 : Blo 1156638 40067131 := bstep (se 1 (by rfl) ⟨30050348, by rfl⟩ : syracuseStep 40067131 = 60100697) B60100697
theorem B1565087 : Blo 1156638 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B1302943 : Blo 1156638 1302943 := bstep (se 1 (by rfl) ⟨977207, by rfl⟩ : syracuseStep 1302943 = 1954415) B1954415
theorem B1958303 : Blo 1156638 1958303 := bstep (se 1 (by rfl) ⟨1468727, by rfl⟩ : syracuseStep 1958303 = 2937455) B2937455
theorem B1958431 : Blo 1156638 1958431 := bstep (se 1 (by rfl) ⟨1468823, by rfl⟩ : syracuseStep 1958431 = 2937647) B2937647
theorem B1467391 : Blo 1156638 1467391 := bstep (se 1 (by rfl) ⟨1100543, by rfl⟩ : syracuseStep 1467391 = 2201087) B2201087
theorem B19818593 : Blo 1156638 19818593 := bstep (se 2 (by rfl) ⟨7431972, by rfl⟩ : syracuseStep 19818593 = 14863945) B14863945
theorem B1304743 : Blo 1156638 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B5564639 : Blo 1156638 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B29681963 : Blo 1156638 29681963 := bstep (se 1 (by rfl) ⟨22261472, by rfl⟩ : syracuseStep 29681963 = 44522945) B44522945
theorem B1305247 : Blo 1156638 1305247 := bstep (se 1 (by rfl) ⟨978935, by rfl⟩ : syracuseStep 1305247 = 1957871) B1957871
theorem B75099257 : Blo 1156638 75099257 := bstep (se 2 (by rfl) ⟨28162221, by rfl⟩ : syracuseStep 75099257 = 56324443) B56324443
theorem B12512393 : Blo 1156638 12512393 := bstep (se 2 (by rfl) ⟨4692147, by rfl⟩ : syracuseStep 12512393 = 9384295) B9384295
theorem B3960863 : Blo 1156638 3960863 := bstep (se 1 (by rfl) ⟨2970647, by rfl⟩ : syracuseStep 3960863 = 5941295) B5941295
theorem B3960971 : Blo 1156638 3960971 := bstep (se 1 (by rfl) ⟨2970728, by rfl⟩ : syracuseStep 3960971 = 5941457) B5941457
theorem B6254813 : Blo 1156638 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B8811179 : Blo 1156638 8811179 := bstep (se 1 (by rfl) ⟨6608384, by rfl⟩ : syracuseStep 8811179 = 13216769) B13216769
theorem B5010541 : Blo 1156638 5010541 := bstep (se 3 (by rfl) ⟨939476, by rfl⟩ : syracuseStep 5010541 = 1878953) B1878953
theorem B5567753 : Blo 1156638 5567753 := bstep (se 2 (by rfl) ⟨2087907, by rfl⟩ : syracuseStep 5567753 = 4175815) B4175815
theorem B5010785 : Blo 1156638 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B23787179 : Blo 1156638 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B8353793 : Blo 1156638 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B6256763 : Blo 1156638 6256763 := bstep (se 1 (by rfl) ⟨4692572, by rfl⟩ : syracuseStep 6256763 = 9385145) B9385145
theorem B9042151 : Blo 1156638 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B13400423 : Blo 1156638 13400423 := bstep (se 1 (by rfl) ⟨10050317, by rfl⟩ : syracuseStep 13400423 = 20100635) B20100635
theorem B1735049 : Blo 1156638 1735049 := bstep (se 2 (by rfl) ⟨650643, by rfl⟩ : syracuseStep 1735049 = 1301287) B1301287
theorem B1735223 : Blo 1156638 1735223 := bstep (se 1 (by rfl) ⟨1301417, by rfl⟩ : syracuseStep 1735223 = 2602835) B2602835
theorem B16906843 : Blo 1156638 16906843 := bstep (se 1 (by rfl) ⟨12680132, by rfl⟩ : syracuseStep 16906843 = 25360265) B25360265
theorem B1735295 : Blo 1156638 1735295 := bstep (se 1 (by rfl) ⟨1301471, by rfl⟩ : syracuseStep 1735295 = 2602943) B2602943
theorem B20085407 : Blo 1156638 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B67697491 : Blo 1156638 67697491 := bstep (se 1 (by rfl) ⟨50773118, by rfl⟩ : syracuseStep 67697491 = 101546237) B101546237
theorem B1735673 : Blo 1156638 1735673 := bstep (se 2 (by rfl) ⟨650877, by rfl⟩ : syracuseStep 1735673 = 1301755) B1301755
theorem B7535711 : Blo 1156638 7535711 := bstep (se 1 (by rfl) ⟨5651783, by rfl⟩ : syracuseStep 7535711 = 11303567) B11303567
theorem B51412151 : Blo 1156638 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B17169965 : Blo 1156638 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B80347085 : Blo 1156638 80347085 := bstep (se 3 (by rfl) ⟨15065078, by rfl⟩ : syracuseStep 80347085 = 30130157) B30130157
theorem B1736681 : Blo 1156638 1736681 := bstep (se 2 (by rfl) ⟨651255, by rfl⟩ : syracuseStep 1736681 = 1302511) B1302511
theorem B1736699 : Blo 1156638 1736699 := bstep (se 1 (by rfl) ⟨1302524, by rfl⟩ : syracuseStep 1736699 = 2605049) B2605049
theorem B14844059 : Blo 1156638 14844059 := bstep (se 1 (by rfl) ⟨11133044, by rfl⟩ : syracuseStep 14844059 = 22266089) B22266089
theorem B1737257 : Blo 1156638 1737257 := bstep (se 2 (by rfl) ⟨651471, by rfl⟩ : syracuseStep 1737257 = 1302943) B1302943
theorem B1738331 : Blo 1156638 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B3966695 : Blo 1156638 3966695 := bstep (se 1 (by rfl) ⟨2975021, by rfl⟩ : syracuseStep 3966695 = 5950043) B5950043
theorem B3344839 : Blo 1156638 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B2198171 : Blo 1156638 2198171 := bstep (se 1 (by rfl) ⟨1648628, by rfl⟩ : syracuseStep 2198171 = 3297257) B3297257
theorem B1739495 : Blo 1156638 1739495 := bstep (se 1 (by rfl) ⟨1304621, by rfl⟩ : syracuseStep 1739495 = 2609243) B2609243
theorem B1739657 : Blo 1156638 1739657 := bstep (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) B1304743
theorem B1740329 : Blo 1156638 1740329 := bstep (se 2 (by rfl) ⟨652623, by rfl⟩ : syracuseStep 1740329 = 1305247) B1305247
theorem B11898683 : Blo 1156638 11898683 := bstep (se 1 (by rfl) ⟨8924012, by rfl⟩ : syracuseStep 11898683 = 17848025) B17848025
theorem B5574595 : Blo 1156638 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B2199545 : Blo 1156638 2199545 := bstep (se 2 (by rfl) ⟨824829, by rfl⟩ : syracuseStep 2199545 = 1649659) B1649659
theorem B2200745 : Blo 1156638 2200745 := bstep (se 2 (by rfl) ⟨825279, by rfl⟩ : syracuseStep 2200745 = 1650559) B1650559
theorem B11147003 : Blo 1156638 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B5871689 : Blo 1156638 5871689 := bstep (se 2 (by rfl) ⟨2201883, by rfl⟩ : syracuseStep 5871689 = 4403767) B4403767
theorem B4397723 : Blo 1156638 4397723 := bstep (se 1 (by rfl) ⟨3298292, by rfl⟩ : syracuseStep 4397723 = 6596585) B6596585
theorem B13212395 : Blo 1156638 13212395 := bstep (se 1 (by rfl) ⟨9909296, by rfl⟩ : syracuseStep 13212395 = 19818593) B19818593
theorem B4169875 : Blo 1156638 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B20095229 : Blo 1156638 20095229 := bstep (se 3 (by rfl) ⟨3767855, by rfl⟩ : syracuseStep 20095229 = 7535711) B7535711
theorem B5874119 : Blo 1156638 5874119 := bstep (se 1 (by rfl) ⟨4405589, by rfl⟩ : syracuseStep 5874119 = 8811179) B8811179
theorem B5874281 : Blo 1156638 5874281 := bstep (se 2 (by rfl) ⟨2202855, by rfl⟩ : syracuseStep 5874281 = 4405711) B4405711
theorem B3711835 : Blo 1156638 3711835 := bstep (se 1 (by rfl) ⟨2783876, by rfl⟩ : syracuseStep 3711835 = 5567753) B5567753
theorem B11150729 : Blo 1156638 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B4171175 : Blo 1156638 4171175 := bstep (se 1 (by rfl) ⟨3128381, by rfl⟩ : syracuseStep 4171175 = 6256763) B6256763
theorem B1156699 : Blo 1156638 1156699 := bstep (se 1 (by rfl) ⟨867524, by rfl⟩ : syracuseStep 1156699 = 1735049) B1735049
theorem B1156815 : Blo 1156638 1156815 := bstep (se 1 (by rfl) ⟨867611, by rfl⟩ : syracuseStep 1156815 = 1735223) B1735223
theorem B1156863 : Blo 1156638 1156863 := bstep (se 1 (by rfl) ⟨867647, by rfl⟩ : syracuseStep 1156863 = 1735295) B1735295
theorem B16721711 : Blo 1156638 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B1157115 : Blo 1156638 1157115 := bstep (se 1 (by rfl) ⟨867836, by rfl⟩ : syracuseStep 1157115 = 1735673) B1735673
theorem B11446643 : Blo 1156638 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B1157787 : Blo 1156638 1157787 := bstep (se 1 (by rfl) ⟨868340, by rfl⟩ : syracuseStep 1157787 = 1736681) B1736681
theorem B1157799 : Blo 1156638 1157799 := bstep (se 1 (by rfl) ⟨868349, by rfl⟩ : syracuseStep 1157799 = 1736699) B1736699
theorem B1157839 : Blo 1156638 1157839 := bstep (se 1 (by rfl) ⟨868379, by rfl⟩ : syracuseStep 1157839 = 1736759) B1736759
theorem B1157863 : Blo 1156638 1157863 := bstep (se 1 (by rfl) ⟨868397, by rfl⟩ : syracuseStep 1157863 = 1736795) B1736795
theorem B53422841 : Blo 1156638 53422841 := bstep (se 2 (by rfl) ⟨20033565, by rfl⟩ : syracuseStep 53422841 = 40067131) B40067131
theorem B1157919 : Blo 1156638 1157919 := bstep (se 1 (by rfl) ⟨868439, by rfl⟩ : syracuseStep 1157919 = 1736879) B1736879
theorem B19770479 : Blo 1156638 19770479 := bstep (se 1 (by rfl) ⟨14827859, by rfl⟩ : syracuseStep 19770479 = 29655719) B29655719
theorem B1322095 : Blo 1156638 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B1158311 : Blo 1156638 1158311 := bstep (se 1 (by rfl) ⟨868733, by rfl⟩ : syracuseStep 1158311 = 1737467) B1737467
theorem B1158399 : Blo 1156638 1158399 := bstep (se 1 (by rfl) ⟨868799, by rfl⟩ : syracuseStep 1158399 = 1737599) B1737599
theorem B21146923 : Blo 1156638 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B6598043 : Blo 1156638 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B101461733 : Blo 1156638 101461733 := bstep (se 4 (by rfl) ⟨9512037, by rfl⟩ : syracuseStep 101461733 = 19024075) B19024075
theorem B25046927 : Blo 1156638 25046927 := bstep (se 1 (by rfl) ⟨18785195, by rfl⟩ : syracuseStep 25046927 = 37570391) B37570391
theorem B1322951 : Blo 1156638 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B1159199 : Blo 1156638 1159199 := bstep (se 1 (by rfl) ⟨869399, by rfl⟩ : syracuseStep 1159199 = 1738799) B1738799
theorem B6271121 : Blo 1156638 6271121 := bstep (se 2 (by rfl) ⟨2351670, by rfl⟩ : syracuseStep 6271121 = 4703341) B4703341
theorem B1159679 : Blo 1156638 1159679 := bstep (se 1 (by rfl) ⟨869759, by rfl⟩ : syracuseStep 1159679 = 1739519) B1739519
theorem B3912569 : Blo 1156638 3912569 := bstep (se 2 (by rfl) ⟨1467213, by rfl⟩ : syracuseStep 3912569 = 2934427) B2934427
theorem B1160303 : Blo 1156638 1160303 := bstep (se 1 (by rfl) ⟨870227, by rfl⟩ : syracuseStep 1160303 = 1740455) B1740455
theorem B1160383 : Blo 1156638 1160383 := bstep (se 1 (by rfl) ⟨870287, by rfl⟩ : syracuseStep 1160383 = 1740575) B1740575
theorem B1160415 : Blo 1156638 1160415 := bstep (se 1 (by rfl) ⟨870311, by rfl⟩ : syracuseStep 1160415 = 1740623) B1740623
theorem B1160495 : Blo 1156638 1160495 := bstep (se 1 (by rfl) ⟨870371, by rfl⟩ : syracuseStep 1160495 = 1740743) B1740743
theorem B2602475 : Blo 1156638 2602475 := bstep (se 1 (by rfl) ⟨1951856, by rfl⟩ : syracuseStep 2602475 = 3903713) B3903713
theorem B2930863 : Blo 1156638 2930863 := bstep (se 1 (by rfl) ⟨2198147, by rfl⟩ : syracuseStep 2930863 = 4396295) B4396295
theorem B2472191 : Blo 1156638 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B2472353 : Blo 1156638 2472353 := bstep (se 2 (by rfl) ⟨927132, by rfl⟩ : syracuseStep 2472353 = 1854265) B1854265
theorem B6601459 : Blo 1156638 6601459 := bstep (se 1 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 6601459 = 9902189) B9902189
theorem B2505575 : Blo 1156638 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B2603879 : Blo 1156638 2603879 := bstep (se 1 (by rfl) ⟨1952909, by rfl⟩ : syracuseStep 2603879 = 3905819) B3905819
theorem B2505583 : Blo 1156638 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B16694261 : Blo 1156638 16694261 := bstep (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) B1565087
theorem B2604059 : Blo 1156638 2604059 := bstep (se 1 (by rfl) ⟨1953044, by rfl⟩ : syracuseStep 2604059 = 3906089) B3906089
theorem B2931785 : Blo 1156638 2931785 := bstep (se 2 (by rfl) ⟨1099419, by rfl⟩ : syracuseStep 2931785 = 2198839) B2198839
theorem B2604527 : Blo 1156638 2604527 := bstep (se 1 (by rfl) ⟨1953395, by rfl⟩ : syracuseStep 2604527 = 3906791) B3906791
theorem B6602735 : Blo 1156638 6602735 := bstep (se 1 (by rfl) ⟨4952051, by rfl⟩ : syracuseStep 6602735 = 9904103) B9904103
theorem B2605625 : Blo 1156638 2605625 := bstep (se 2 (by rfl) ⟨977109, by rfl⟩ : syracuseStep 2605625 = 1954219) B1954219
theorem B26722885 : Blo 1156638 26722885 := bstep (se 4 (by rfl) ⟨2505270, by rfl⟩ : syracuseStep 26722885 = 5010541) B5010541
theorem B12698855 : Blo 1156638 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B2606345 : Blo 1156638 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B9291455 : Blo 1156638 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B2607083 : Blo 1156638 2607083 := bstep (se 1 (by rfl) ⟨1955312, by rfl⟩ : syracuseStep 2607083 = 3910625) B3910625
theorem B8341595 : Blo 1156638 8341595 := bstep (se 1 (by rfl) ⟨6256196, by rfl⟩ : syracuseStep 8341595 = 12512393) B12512393
theorem B2607227 : Blo 1156638 2607227 := bstep (se 1 (by rfl) ⟨1955420, by rfl⟩ : syracuseStep 2607227 = 3910841) B3910841
theorem B2607335 : Blo 1156638 2607335 := bstep (se 1 (by rfl) ⟨1955501, by rfl⟩ : syracuseStep 2607335 = 3911003) B3911003
theorem B2640575 : Blo 1156638 2640575 := bstep (se 1 (by rfl) ⟨1980431, by rfl⟩ : syracuseStep 2640575 = 3960863) B3960863
theorem B1952491 : Blo 1156638 1952491 := bstep (se 1 (by rfl) ⟨1464368, by rfl⟩ : syracuseStep 1952491 = 2928737) B2928737
theorem B2640647 : Blo 1156638 2640647 := bstep (se 1 (by rfl) ⟨1980485, by rfl⟩ : syracuseStep 2640647 = 3960971) B3960971
theorem B45763865 : Blo 1156638 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B1953247 : Blo 1156638 1953247 := bstep (se 1 (by rfl) ⟨1464935, by rfl⟩ : syracuseStep 1953247 = 2929871) B2929871
theorem B2608667 : Blo 1156638 2608667 := bstep (se 1 (by rfl) ⟨1956500, by rfl⟩ : syracuseStep 2608667 = 3913001) B3913001
theorem B2936351 : Blo 1156638 2936351 := bstep (se 1 (by rfl) ⟨2202263, by rfl⟩ : syracuseStep 2936351 = 4404527) B4404527
theorem B90263321 : Blo 1156638 90263321 := bstep (se 2 (by rfl) ⟨33848745, by rfl⟩ : syracuseStep 90263321 = 67697491) B67697491
theorem B2609063 : Blo 1156638 2609063 := bstep (se 1 (by rfl) ⟨1956797, by rfl⟩ : syracuseStep 2609063 = 3913595) B3913595
theorem B2609225 : Blo 1156638 2609225 := bstep (se 2 (by rfl) ⟨978459, by rfl⟩ : syracuseStep 2609225 = 1956919) B1956919
theorem B2936969 : Blo 1156638 2936969 := bstep (se 2 (by rfl) ⟨1101363, by rfl⟩ : syracuseStep 2936969 = 2202727) B2202727
theorem B8933615 : Blo 1156638 8933615 := bstep (se 1 (by rfl) ⟨6700211, by rfl⟩ : syracuseStep 8933615 = 13400423) B13400423
theorem B13390271 : Blo 1156638 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B2937323 : Blo 1156638 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B2937343 : Blo 1156638 2937343 := bstep (se 1 (by rfl) ⟨2203007, by rfl⟩ : syracuseStep 2937343 = 4406015) B4406015
theorem B2610359 : Blo 1156638 2610359 := bstep (se 1 (by rfl) ⟨1957769, by rfl⟩ : syracuseStep 2610359 = 3915539) B3915539
theorem B53564723 : Blo 1156638 53564723 := bstep (se 1 (by rfl) ⟨40173542, by rfl⟩ : syracuseStep 53564723 = 80347085) B80347085
theorem B14112251 : Blo 1156638 14112251 := bstep (se 1 (by rfl) ⟨10584188, by rfl⟩ : syracuseStep 14112251 = 21168377) B21168377
theorem B2611241 : Blo 1156638 2611241 := bstep (se 2 (by rfl) ⟨979215, by rfl⟩ : syracuseStep 2611241 = 1958431) B1958431
theorem B12507203 : Blo 1156638 12507203 := bstep (se 1 (by rfl) ⟨9380402, by rfl⟩ : syracuseStep 12507203 = 18760805) B18760805
theorem B1956521 : Blo 1156638 1956521 := bstep (se 2 (by rfl) ⟨733695, by rfl⟩ : syracuseStep 1956521 = 1467391) B1467391
theorem B1761161 : Blo 1156638 1761161 := bstep (se 2 (by rfl) ⟨660435, by rfl⟩ : syracuseStep 1761161 = 1320871) B1320871
theorem B1302655 : Blo 1156638 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B1303195 : Blo 1156638 1303195 := bstep (se 1 (by rfl) ⟨977396, by rfl⟩ : syracuseStep 1303195 = 1954793) B1954793
theorem B1303231 : Blo 1156638 1303231 := bstep (se 1 (by rfl) ⟨977423, by rfl⟩ : syracuseStep 1303231 = 1954847) B1954847
theorem B2712671 : Blo 1156638 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B8807777 : Blo 1156638 8807777 := bstep (se 2 (by rfl) ⟨3302916, by rfl⟩ : syracuseStep 8807777 = 6605833) B6605833
theorem B1304167 : Blo 1156638 1304167 := bstep (se 1 (by rfl) ⟨978125, by rfl⟩ : syracuseStep 1304167 = 1956251) B1956251
theorem B192997505 : Blo 1156638 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B22276235 : Blo 1156638 22276235 := bstep (se 1 (by rfl) ⟨16707176, by rfl⟩ : syracuseStep 22276235 = 33414353) B33414353
theorem B812706149 : Blo 1156638 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B8350361 : Blo 1156638 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B22276781 : Blo 1156638 22276781 := bstep (se 3 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 22276781 = 8353793) B8353793
theorem B5565293 : Blo 1156638 5565293 := bstep (se 3 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 5565293 = 2086985) B2086985
theorem B1305535 : Blo 1156638 1305535 := bstep (se 1 (by rfl) ⟨979151, by rfl⟩ : syracuseStep 1305535 = 1958303) B1958303
theorem B14839037 : Blo 1156638 14839037 := bstep (se 3 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 14839037 = 5564639) B5564639
theorem B19787975 : Blo 1156638 19787975 := bstep (se 1 (by rfl) ⟨14840981, by rfl⟩ : syracuseStep 19787975 = 29681963) B29681963
theorem B50066171 : Blo 1156638 50066171 := bstep (se 1 (by rfl) ⟨37549628, by rfl⟩ : syracuseStep 50066171 = 75099257) B75099257
theorem B89158805 : Blo 1156638 89158805 := bstep (se 6 (by rfl) ⟨2089659, by rfl⟩ : syracuseStep 89158805 = 4179319) B4179319
theorem B50034185 : Blo 1156638 50034185 := bstep (se 2 (by rfl) ⟨18762819, by rfl⟩ : syracuseStep 50034185 = 37525639) B37525639
theorem B12056201 : Blo 1156638 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B19036241 : Blo 1156638 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B22542457 : Blo 1156638 22542457 := bstep (se 2 (by rfl) ⟨8453421, by rfl⟩ : syracuseStep 22542457 = 16906843) B16906843
theorem B3340523 : Blo 1156638 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B1735067 : Blo 1156638 1735067 := bstep (se 1 (by rfl) ⟨1301300, by rfl⟩ : syracuseStep 1735067 = 2602601) B2602601
theorem B15858119 : Blo 1156638 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B21133871 : Blo 1156638 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B1735271 : Blo 1156638 1735271 := bstep (se 1 (by rfl) ⟨1301453, by rfl⟩ : syracuseStep 1735271 = 2602907) B2602907
theorem B34274767 : Blo 1156638 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B1736159 : Blo 1156638 1736159 := bstep (se 1 (by rfl) ⟨1302119, by rfl⟩ : syracuseStep 1736159 = 2604239) B2604239
theorem B2784935 : Blo 1156638 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B1736639 : Blo 1156638 1736639 := bstep (se 1 (by rfl) ⟨1302479, by rfl⟩ : syracuseStep 1736639 = 2604959) B2604959
theorem B9896039 : Blo 1156638 9896039 := bstep (se 1 (by rfl) ⟨7422029, by rfl⟩ : syracuseStep 9896039 = 14844059) B14844059
theorem B1736873 : Blo 1156638 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B1737083 : Blo 1156638 1737083 := bstep (se 1 (by rfl) ⟨1302812, by rfl⟩ : syracuseStep 1737083 = 2605625) B2605625
theorem B1737563 : Blo 1156638 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B1737593 : Blo 1156638 1737593 := bstep (se 2 (by rfl) ⟨651597, by rfl⟩ : syracuseStep 1737593 = 1303195) B1303195
theorem B1737641 : Blo 1156638 1737641 := bstep (se 2 (by rfl) ⟨651615, by rfl⟩ : syracuseStep 1737641 = 1303231) B1303231
theorem B4949113 : Blo 1156638 4949113 := bstep (se 2 (by rfl) ⟨1855917, by rfl⟩ : syracuseStep 4949113 = 3711835) B3711835
theorem B6194303 : Blo 1156638 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B1738055 : Blo 1156638 1738055 := bstep (se 1 (by rfl) ⟨1303541, by rfl⟩ : syracuseStep 1738055 = 2607083) B2607083
theorem B1738151 : Blo 1156638 1738151 := bstep (se 1 (by rfl) ⟨1303613, by rfl⟩ : syracuseStep 1738151 = 2607227) B2607227
theorem B1738223 : Blo 1156638 1738223 := bstep (se 1 (by rfl) ⟨1303667, by rfl⟩ : syracuseStep 1738223 = 2607335) B2607335
theorem B1738889 : Blo 1156638 1738889 := bstep (se 2 (by rfl) ⟨652083, by rfl⟩ : syracuseStep 1738889 = 1304167) B1304167
theorem B30509243 : Blo 1156638 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B1739111 : Blo 1156638 1739111 := bstep (se 1 (by rfl) ⟨1304333, by rfl⟩ : syracuseStep 1739111 = 2608667) B2608667
theorem B7932455 : Blo 1156638 7932455 := bstep (se 1 (by rfl) ⟨5949341, by rfl⟩ : syracuseStep 7932455 = 11898683) B11898683
theorem B1739375 : Blo 1156638 1739375 := bstep (se 1 (by rfl) ⟨1304531, by rfl⟩ : syracuseStep 1739375 = 2609063) B2609063
theorem B1739483 : Blo 1156638 1739483 := bstep (se 1 (by rfl) ⟨1304612, by rfl⟩ : syracuseStep 1739483 = 2609225) B2609225
theorem B1740239 : Blo 1156638 1740239 := bstep (se 1 (by rfl) ⟨1305179, by rfl⟩ : syracuseStep 1740239 = 2610359) B2610359
theorem B9408167 : Blo 1156638 9408167 := bstep (se 1 (by rfl) ⟨7056125, by rfl⟩ : syracuseStep 9408167 = 14112251) B14112251
theorem B1740713 : Blo 1156638 1740713 := bstep (se 2 (by rfl) ⟨652767, by rfl⟩ : syracuseStep 1740713 = 1305535) B1305535
theorem B1740827 : Blo 1156638 1740827 := bstep (se 1 (by rfl) ⟨1305620, by rfl⟩ : syracuseStep 1740827 = 2611241) B2611241
theorem B514660013 : Blo 1156638 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B1808447 : Blo 1156638 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B5871851 : Blo 1156638 5871851 := bstep (se 1 (by rfl) ⟨4403888, by rfl⟩ : syracuseStep 5871851 = 8807777) B8807777
theorem B11147807 : Blo 1156638 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B14850823 : Blo 1156638 14850823 := bstep (se 1 (by rfl) ⟨11138117, by rfl⟩ : syracuseStep 14850823 = 22276235) B22276235
theorem B14851187 : Blo 1156638 14851187 := bstep (se 1 (by rfl) ⟨11138390, by rfl⟩ : syracuseStep 14851187 = 22276781) B22276781
theorem B3710195 : Blo 1156638 3710195 := bstep (se 1 (by rfl) ⟨2782646, by rfl⟩ : syracuseStep 3710195 = 5565293) B5565293
theorem B13180319 : Blo 1156638 13180319 := bstep (se 1 (by rfl) ⟨9885239, by rfl⟩ : syracuseStep 13180319 = 19770479) B19770479
theorem B4398695 : Blo 1156638 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B67641155 : Blo 1156638 67641155 := bstep (se 1 (by rfl) ⟨50730866, by rfl⟩ : syracuseStep 67641155 = 101461733) B101461733
theorem B30056609 : Blo 1156638 30056609 := bstep (se 2 (by rfl) ⟨11271228, by rfl⟩ : syracuseStep 30056609 = 22542457) B22542457
theorem B3907817 : Blo 1156638 3907817 := bstep (se 2 (by rfl) ⟨1465431, by rfl⟩ : syracuseStep 3907817 = 2930863) B2930863
theorem B8037467 : Blo 1156638 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B12690827 : Blo 1156638 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B1648127 : Blo 1156638 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B1156711 : Blo 1156638 1156711 := bstep (se 1 (by rfl) ⟨867533, by rfl⟩ : syracuseStep 1156711 = 1735067) B1735067
theorem B1648235 : Blo 1156638 1648235 := bstep (se 1 (by rfl) ⟨1236176, by rfl⟩ : syracuseStep 1648235 = 2472353) B2472353
theorem B1156847 : Blo 1156638 1156847 := bstep (se 1 (by rfl) ⟨867635, by rfl⟩ : syracuseStep 1156847 = 1735271) B1735271
theorem B1157439 : Blo 1156638 1157439 := bstep (se 1 (by rfl) ⟨868079, by rfl⟩ : syracuseStep 1157439 = 1736159) B1736159
theorem B4696429 : Blo 1156638 4696429 := bstep (se 3 (by rfl) ⟨880580, by rfl⟩ : syracuseStep 4696429 = 1761161) B1761161
theorem B1157759 : Blo 1156638 1157759 := bstep (se 1 (by rfl) ⟨868319, by rfl⟩ : syracuseStep 1157759 = 1736639) B1736639
theorem B4401823 : Blo 1156638 4401823 := bstep (se 1 (by rfl) ⟨3301367, by rfl⟩ : syracuseStep 4401823 = 6602735) B6602735
theorem B1158171 : Blo 1156638 1158171 := bstep (se 1 (by rfl) ⟨868628, by rfl⟩ : syracuseStep 1158171 = 1737257) B1737257
theorem B53587277 : Blo 1156638 53587277 := bstep (se 3 (by rfl) ⟨10047614, by rfl⟩ : syracuseStep 53587277 = 20095229) B20095229
theorem B35630513 : Blo 1156638 35630513 := bstep (se 2 (by rfl) ⟨13361442, by rfl⟩ : syracuseStep 35630513 = 26722885) B26722885
theorem B8465903 : Blo 1156638 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B1158887 : Blo 1156638 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B1159663 : Blo 1156638 1159663 := bstep (se 1 (by rfl) ⟨869747, by rfl⟩ : syracuseStep 1159663 = 1739495) B1739495
theorem B1159771 : Blo 1156638 1159771 := bstep (se 1 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 1159771 = 1739657) B1739657
theorem B1160219 : Blo 1156638 1160219 := bstep (se 1 (by rfl) ⟨870164, by rfl⟩ : syracuseStep 1160219 = 1740329) B1740329
theorem B60175547 : Blo 1156638 60175547 := bstep (se 1 (by rfl) ⟨45131660, by rfl⟩ : syracuseStep 60175547 = 90263321) B90263321
theorem B8926847 : Blo 1156638 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B2603321 : Blo 1156638 2603321 := bstep (se 2 (by rfl) ⟨976245, by rfl⟩ : syracuseStep 2603321 = 1952491) B1952491
theorem B8338135 : Blo 1156638 8338135 := bstep (se 1 (by rfl) ⟨6253601, by rfl⟩ : syracuseStep 8338135 = 12507203) B12507203
theorem B3914459 : Blo 1156638 3914459 := bstep (se 1 (by rfl) ⟨2935844, by rfl⟩ : syracuseStep 3914459 = 5871689) B5871689
theorem B2931815 : Blo 1156638 2931815 := bstep (se 1 (by rfl) ⟨2198861, by rfl⟩ : syracuseStep 2931815 = 4397723) B4397723
theorem B2604329 : Blo 1156638 2604329 := bstep (se 2 (by rfl) ⟨976623, by rfl⟩ : syracuseStep 2604329 = 1953247) B1953247
theorem B3916079 : Blo 1156638 3916079 := bstep (se 1 (by rfl) ⟨2937059, by rfl⟩ : syracuseStep 3916079 = 5874119) B5874119
theorem B3916187 : Blo 1156638 3916187 := bstep (se 1 (by rfl) ⟨2937140, by rfl⟩ : syracuseStep 3916187 = 5874281) B5874281
theorem B3916457 : Blo 1156638 3916457 := bstep (se 2 (by rfl) ⟨1468671, by rfl⟩ : syracuseStep 3916457 = 2937343) B2937343
theorem B30524381 : Blo 1156638 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B541804099 : Blo 1156638 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B16697951 : Blo 1156638 16697951 := bstep (se 1 (by rfl) ⟨12523463, by rfl⟩ : syracuseStep 16697951 = 25046927) B25046927
theorem B4180747 : Blo 1156638 4180747 := bstep (se 1 (by rfl) ⟨3135560, by rfl⟩ : syracuseStep 4180747 = 6271121) B6271121
theorem B13191983 : Blo 1156638 13191983 := bstep (se 1 (by rfl) ⟨9893987, by rfl⟩ : syracuseStep 13191983 = 19787975) B19787975
theorem B33377447 : Blo 1156638 33377447 := bstep (se 1 (by rfl) ⟨25033085, by rfl⟩ : syracuseStep 33377447 = 50066171) B50066171
theorem B2608379 : Blo 1156638 2608379 := bstep (se 1 (by rfl) ⟨1956284, by rfl⟩ : syracuseStep 2608379 = 3912569) B3912569
theorem B8801945 : Blo 1156638 8801945 := bstep (se 2 (by rfl) ⟨3300729, by rfl⟩ : syracuseStep 8801945 = 6601459) B6601459
theorem B71356565 : Blo 1156638 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B10572079 : Blo 1156638 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B45699689 : Blo 1156638 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B11129507 : Blo 1156638 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B1954523 : Blo 1156638 1954523 := bstep (se 1 (by rfl) ⟨1465892, by rfl⟩ : syracuseStep 1954523 = 2931785) B2931785
theorem B1856623 : Blo 1156638 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B3527869 : Blo 1156638 3527869 := bstep (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) B1322951
theorem B5559833 : Blo 1156638 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B2644463 : Blo 1156638 2644463 := bstep (se 1 (by rfl) ⟨1983347, by rfl⟩ : syracuseStep 2644463 = 3966695) B3966695
theorem B5561063 : Blo 1156638 5561063 := bstep (se 1 (by rfl) ⟨4170797, by rfl⟩ : syracuseStep 5561063 = 8341595) B8341595
theorem B1465447 : Blo 1156638 1465447 := bstep (se 1 (by rfl) ⟨1099085, by rfl⟩ : syracuseStep 1465447 = 2198171) B2198171
theorem B1760383 : Blo 1156638 1760383 := bstep (se 1 (by rfl) ⟨1320287, by rfl⟩ : syracuseStep 1760383 = 2640575) B2640575
theorem B1957567 : Blo 1156638 1957567 := bstep (se 1 (by rfl) ⟨1468175, by rfl⟩ : syracuseStep 1957567 = 2936351) B2936351
theorem B1466363 : Blo 1156638 1466363 := bstep (se 1 (by rfl) ⟨1099772, by rfl⟩ : syracuseStep 1466363 = 2199545) B2199545
theorem B1957979 : Blo 1156638 1957979 := bstep (se 1 (by rfl) ⟨1468484, by rfl⟩ : syracuseStep 1957979 = 2936969) B2936969
theorem B5955743 : Blo 1156638 5955743 := bstep (se 1 (by rfl) ⟨4466807, by rfl⟩ : syracuseStep 5955743 = 8933615) B8933615
theorem B1958215 : Blo 1156638 1958215 := bstep (se 1 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 1958215 = 2937323) B2937323
theorem B1467163 : Blo 1156638 1467163 := bstep (se 1 (by rfl) ⟨1100372, by rfl⟩ : syracuseStep 1467163 = 2200745) B2200745
theorem B35709815 : Blo 1156638 35709815 := bstep (se 1 (by rfl) ⟨26782361, by rfl⟩ : syracuseStep 35709815 = 53564723) B53564723
theorem B7431335 : Blo 1156638 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B1762793 : Blo 1156638 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B1304347 : Blo 1156638 1304347 := bstep (se 1 (by rfl) ⟨978260, by rfl⟩ : syracuseStep 1304347 = 1956521) B1956521
theorem B8808263 : Blo 1156638 8808263 := bstep (se 1 (by rfl) ⟨6606197, by rfl⟩ : syracuseStep 8808263 = 13212395) B13212395
theorem B7432793 : Blo 1156638 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B8908061 : Blo 1156638 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B7433819 : Blo 1156638 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B2780783 : Blo 1156638 2780783 := bstep (se 1 (by rfl) ⟨2085587, by rfl⟩ : syracuseStep 2780783 = 4171175) B4171175
theorem B112783589 : Blo 1156638 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B5566907 : Blo 1156638 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B35615227 : Blo 1156638 35615227 := bstep (se 1 (by rfl) ⟨26711420, by rfl⟩ : syracuseStep 35615227 = 53422841) B53422841
theorem B7041725 : Blo 1156638 7041725 := bstep (se 3 (by rfl) ⟨1320323, by rfl⟩ : syracuseStep 7041725 = 2640647) B2640647
theorem B9892691 : Blo 1156638 9892691 := bstep (se 1 (by rfl) ⟨7419518, by rfl⟩ : syracuseStep 9892691 = 14839037) B14839037
theorem B6681533 : Blo 1156638 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B59439203 : Blo 1156638 59439203 := bstep (se 1 (by rfl) ⟨44579402, by rfl⟩ : syracuseStep 59439203 = 89158805) B89158805
theorem B1734983 : Blo 1156638 1734983 := bstep (se 1 (by rfl) ⟨1301237, by rfl⟩ : syracuseStep 1734983 = 2602475) B2602475
theorem B33356123 : Blo 1156638 33356123 := bstep (se 1 (by rfl) ⟨25017092, by rfl⟩ : syracuseStep 33356123 = 50034185) B50034185
theorem B3340777 : Blo 1156638 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B14089247 : Blo 1156638 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B1735919 : Blo 1156638 1735919 := bstep (se 1 (by rfl) ⟨1301939, by rfl⟩ : syracuseStep 1735919 = 2603879) B2603879
theorem B1736039 : Blo 1156638 1736039 := bstep (se 1 (by rfl) ⟨1302029, by rfl⟩ : syracuseStep 1736039 = 2604059) B2604059
theorem B1736351 : Blo 1156638 1736351 := bstep (se 1 (by rfl) ⟨1302263, by rfl⟩ : syracuseStep 1736351 = 2604527) B2604527
theorem B190284173 : Blo 1156638 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B20349587 : Blo 1156638 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B4129535 : Blo 1156638 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B722405465 : Blo 1156638 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B22251631 : Blo 1156638 22251631 := bstep (se 1 (by rfl) ⟨16688723, by rfl⟩ : syracuseStep 22251631 = 33377447) B33377447
theorem B1738919 : Blo 1156638 1738919 := bstep (se 1 (by rfl) ⟨1304189, by rfl⟩ : syracuseStep 1738919 = 2608379) B2608379
theorem B1739129 : Blo 1156638 1739129 := bstep (se 2 (by rfl) ⟨652173, by rfl⟩ : syracuseStep 1739129 = 1304347) B1304347
theorem B5867963 : Blo 1156638 5867963 := bstep (se 1 (by rfl) ⟨4400972, by rfl⟩ : syracuseStep 5867963 = 8801945) B8801945
theorem B6261905 : Blo 1156638 6261905 := bstep (se 2 (by rfl) ⟨2348214, by rfl⟩ : syracuseStep 6261905 = 4696429) B4696429
theorem B5869097 : Blo 1156638 5869097 := bstep (se 2 (by rfl) ⟨2200911, by rfl⟩ : syracuseStep 5869097 = 4401823) B4401823
theorem B5574329 : Blo 1156638 5574329 := bstep (se 2 (by rfl) ⟨2090373, by rfl⟩ : syracuseStep 5574329 = 4180747) B4180747
theorem B3706555 : Blo 1156638 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B4395005 : Blo 1156638 4395005 := bstep (se 3 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 4395005 = 1648127) B1648127
theorem B4395293 : Blo 1156638 4395293 := bstep (se 3 (by rfl) ⟨824117, by rfl⟩ : syracuseStep 4395293 = 1648235) B1648235
theorem B3707375 : Blo 1156638 3707375 := bstep (se 1 (by rfl) ⟨2780531, by rfl⟩ : syracuseStep 3707375 = 5561063) B5561063
theorem B9900791 : Blo 1156638 9900791 := bstep (se 1 (by rfl) ⟨7425593, by rfl⟩ : syracuseStep 9900791 = 14851187) B14851187
theorem B8786879 : Blo 1156638 8786879 := bstep (se 1 (by rfl) ⟨6590159, by rfl⟩ : syracuseStep 8786879 = 13180319) B13180319
theorem B45094103 : Blo 1156638 45094103 := bstep (se 1 (by rfl) ⟨33820577, by rfl⟩ : syracuseStep 45094103 = 67641155) B67641155
theorem B3970495 : Blo 1156638 3970495 := bstep (se 1 (by rfl) ⟨2977871, by rfl⟩ : syracuseStep 3970495 = 5955743) B5955743
theorem B4822525 : Blo 1156638 4822525 := bstep (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) B1808447
theorem B14096105 : Blo 1156638 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B47486969 : Blo 1156638 47486969 := bstep (se 2 (by rfl) ⟨17807613, by rfl⟩ : syracuseStep 47486969 = 35615227) B35615227
theorem B4954223 : Blo 1156638 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B8460551 : Blo 1156638 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B5872175 : Blo 1156638 5872175 := bstep (se 1 (by rfl) ⟨4404131, by rfl⟩ : syracuseStep 5872175 = 8808263) B8808263
theorem B4955195 : Blo 1156638 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B35724851 : Blo 1156638 35724851 := bstep (se 1 (by rfl) ⟨26793638, by rfl⟩ : syracuseStep 35724851 = 53587277) B53587277
theorem B5643935 : Blo 1156638 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B4955879 : Blo 1156638 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B3711271 : Blo 1156638 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B4694483 : Blo 1156638 4694483 := bstep (se 1 (by rfl) ⟨3520862, by rfl⟩ : syracuseStep 4694483 = 7041725) B7041725
theorem B6595127 : Blo 1156638 6595127 := bstep (se 1 (by rfl) ⟨4946345, by rfl⟩ : syracuseStep 6595127 = 9892691) B9892691
theorem B40117031 : Blo 1156638 40117031 := bstep (se 1 (by rfl) ⟨30087773, by rfl⟩ : syracuseStep 40117031 = 60175547) B60175547
theorem B11117513 : Blo 1156638 11117513 := bstep (se 2 (by rfl) ⟨4169067, by rfl⟩ : syracuseStep 11117513 = 8338135) B8338135
theorem B19801097 : Blo 1156638 19801097 := bstep (se 2 (by rfl) ⟨7425411, by rfl⟩ : syracuseStep 19801097 = 14850823) B14850823
theorem B39626135 : Blo 1156638 39626135 := bstep (se 1 (by rfl) ⟨29719601, by rfl⟩ : syracuseStep 39626135 = 59439203) B59439203
theorem B1156655 : Blo 1156638 1156655 := bstep (se 1 (by rfl) ⟨867491, by rfl⟩ : syracuseStep 1156655 = 1734983) B1734983
theorem B1157279 : Blo 1156638 1157279 := bstep (se 1 (by rfl) ⟨867959, by rfl⟩ : syracuseStep 1157279 = 1735919) B1735919
theorem B1157359 : Blo 1156638 1157359 := bstep (se 1 (by rfl) ⟨868019, by rfl⟩ : syracuseStep 1157359 = 1736039) B1736039
theorem B1157567 : Blo 1156638 1157567 := bstep (se 1 (by rfl) ⟨868175, by rfl⟩ : syracuseStep 1157567 = 1736351) B1736351
theorem B3910301 : Blo 1156638 3910301 := bstep (se 3 (by rfl) ⟨733181, by rfl⟩ : syracuseStep 3910301 = 1466363) B1466363
theorem B6597359 : Blo 1156638 6597359 := bstep (se 1 (by rfl) ⟨4948019, by rfl⟩ : syracuseStep 6597359 = 9896039) B9896039
theorem B1157915 : Blo 1156638 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B1158055 : Blo 1156638 1158055 := bstep (se 1 (by rfl) ⟨868541, by rfl⟩ : syracuseStep 1158055 = 1737083) B1737083
theorem B1158375 : Blo 1156638 1158375 := bstep (se 1 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 1158375 = 1737563) B1737563
theorem B1158395 : Blo 1156638 1158395 := bstep (se 1 (by rfl) ⟨868796, by rfl⟩ : syracuseStep 1158395 = 1737593) B1737593
theorem B1158427 : Blo 1156638 1158427 := bstep (se 1 (by rfl) ⟨868820, by rfl⟩ : syracuseStep 1158427 = 1737641) B1737641
theorem B1158703 : Blo 1156638 1158703 := bstep (se 1 (by rfl) ⟨869027, by rfl⟩ : syracuseStep 1158703 = 1738055) B1738055
theorem B1158767 : Blo 1156638 1158767 := bstep (se 1 (by rfl) ⟨869075, by rfl⟩ : syracuseStep 1158767 = 1738151) B1738151
theorem B1158815 : Blo 1156638 1158815 := bstep (se 1 (by rfl) ⟨869111, by rfl⟩ : syracuseStep 1158815 = 1738223) B1738223
theorem B1159259 : Blo 1156638 1159259 := bstep (se 1 (by rfl) ⟨869444, by rfl⟩ : syracuseStep 1159259 = 1738889) B1738889
theorem B6598817 : Blo 1156638 6598817 := bstep (se 2 (by rfl) ⟨2474556, by rfl⟩ : syracuseStep 6598817 = 4949113) B4949113
theorem B1159407 : Blo 1156638 1159407 := bstep (se 1 (by rfl) ⟨869555, by rfl⟩ : syracuseStep 1159407 = 1739111) B1739111
theorem B5288303 : Blo 1156638 5288303 := bstep (se 1 (by rfl) ⟨3966227, by rfl⟩ : syracuseStep 5288303 = 7932455) B7932455
theorem B1159583 : Blo 1156638 1159583 := bstep (se 1 (by rfl) ⟨869687, by rfl⟩ : syracuseStep 1159583 = 1739375) B1739375
theorem B1159655 : Blo 1156638 1159655 := bstep (se 1 (by rfl) ⟨869741, by rfl⟩ : syracuseStep 1159655 = 1739483) B1739483
theorem B8794655 : Blo 1156638 8794655 := bstep (se 1 (by rfl) ⟨6595991, by rfl⟩ : syracuseStep 8794655 = 13191983) B13191983
theorem B1160159 : Blo 1156638 1160159 := bstep (se 1 (by rfl) ⟨870119, by rfl⟩ : syracuseStep 1160159 = 1740239) B1740239
theorem B6272111 : Blo 1156638 6272111 := bstep (se 1 (by rfl) ⟨4704083, by rfl⟩ : syracuseStep 6272111 = 9408167) B9408167
theorem B1160475 : Blo 1156638 1160475 := bstep (se 1 (by rfl) ⟨870356, by rfl⟩ : syracuseStep 1160475 = 1740713) B1740713
theorem B1160551 : Blo 1156638 1160551 := bstep (se 1 (by rfl) ⟨870413, by rfl⟩ : syracuseStep 1160551 = 1740827) B1740827
theorem B7419671 : Blo 1156638 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B3914567 : Blo 1156638 3914567 := bstep (se 1 (by rfl) ⟨2935925, by rfl⟩ : syracuseStep 3914567 = 5871851) B5871851
theorem B2473463 : Blo 1156638 2473463 := bstep (se 1 (by rfl) ⟨1855097, by rfl⟩ : syracuseStep 2473463 = 3710195) B3710195
theorem B2932463 : Blo 1156638 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B20037739 : Blo 1156638 20037739 := bstep (se 1 (by rfl) ⟨15028304, by rfl⟩ : syracuseStep 20037739 = 30056609) B30056609
theorem B2605211 : Blo 1156638 2605211 := bstep (se 1 (by rfl) ⟨1953908, by rfl⟩ : syracuseStep 2605211 = 3907817) B3907817
theorem B23806543 : Blo 1156638 23806543 := bstep (se 1 (by rfl) ⟨17854907, by rfl⟩ : syracuseStep 23806543 = 35709815) B35709815
theorem B9388709 : Blo 1156638 9388709 := bstep (se 4 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 9388709 = 1760383) B1760383
theorem B5358311 : Blo 1156638 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B2475497 : Blo 1156638 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B4703825 : Blo 1156638 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B1853855 : Blo 1156638 1853855 := bstep (se 1 (by rfl) ⟨1390391, by rfl⟩ : syracuseStep 1853855 = 2780783) B2780783
theorem B75189059 : Blo 1156638 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B5951231 : Blo 1156638 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B1953929 : Blo 1156638 1953929 := bstep (se 2 (by rfl) ⟨732723, by rfl⟩ : syracuseStep 1953929 = 1465447) B1465447
theorem B22237415 : Blo 1156638 22237415 := bstep (se 1 (by rfl) ⟨16678061, by rfl⟩ : syracuseStep 22237415 = 33356123) B33356123
theorem B2609639 : Blo 1156638 2609639 := bstep (se 1 (by rfl) ⟨1957229, by rfl⟩ : syracuseStep 2609639 = 3914459) B3914459
theorem B9392831 : Blo 1156638 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B1954543 : Blo 1156638 1954543 := bstep (se 1 (by rfl) ⟨1465907, by rfl⟩ : syracuseStep 1954543 = 2931815) B2931815
theorem B2610089 : Blo 1156638 2610089 := bstep (se 2 (by rfl) ⟨978783, by rfl⟩ : syracuseStep 2610089 = 1957567) B1957567
theorem B2610719 : Blo 1156638 2610719 := bstep (se 1 (by rfl) ⟨1958039, by rfl⟩ : syracuseStep 2610719 = 3916079) B3916079
theorem B2610791 : Blo 1156638 2610791 := bstep (se 1 (by rfl) ⟨1958093, by rfl⟩ : syracuseStep 2610791 = 3916187) B3916187
theorem B2610953 : Blo 1156638 2610953 := bstep (se 2 (by rfl) ⟨979107, by rfl⟩ : syracuseStep 2610953 = 1958215) B1958215
theorem B2610971 : Blo 1156638 2610971 := bstep (se 1 (by rfl) ⟨1958228, by rfl⟩ : syracuseStep 2610971 = 3916457) B3916457
theorem B1956217 : Blo 1156638 1956217 := bstep (se 2 (by rfl) ⟨733581, by rfl⟩ : syracuseStep 1956217 = 1467163) B1467163
theorem B20339495 : Blo 1156638 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B11131967 : Blo 1156638 11131967 := bstep (se 1 (by rfl) ⟨8348975, by rfl⟩ : syracuseStep 11131967 = 16697951) B16697951
theorem B17817421 : Blo 1156638 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B30466459 : Blo 1156638 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B1303015 : Blo 1156638 1303015 := bstep (se 1 (by rfl) ⟨977261, by rfl⟩ : syracuseStep 1303015 = 1954523) B1954523
theorem B343106675 : Blo 1156638 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B1762975 : Blo 1156638 1762975 := bstep (se 1 (by rfl) ⟨1322231, by rfl⟩ : syracuseStep 1762975 = 2644463) B2644463
theorem B7431871 : Blo 1156638 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B1305319 : Blo 1156638 1305319 := bstep (se 1 (by rfl) ⟨978989, by rfl⟩ : syracuseStep 1305319 = 1957979) B1957979
theorem B1175195 : Blo 1156638 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B23753675 : Blo 1156638 23753675 := bstep (se 1 (by rfl) ⟨17815256, by rfl⟩ : syracuseStep 23753675 = 35630513) B35630513
theorem B4454369 : Blo 1156638 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B23754829 : Blo 1156638 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B1735547 : Blo 1156638 1735547 := bstep (se 1 (by rfl) ⟨1301660, by rfl⟩ : syracuseStep 1735547 = 2603321) B2603321
theorem B1736219 : Blo 1156638 1736219 := bstep (se 1 (by rfl) ⟨1302164, by rfl⟩ : syracuseStep 1736219 = 2604329) B2604329
theorem B1736807 : Blo 1156638 1736807 := bstep (se 1 (by rfl) ⟨1302605, by rfl⟩ : syracuseStep 1736807 = 2605211) B2605211
theorem B4948361 : Blo 1156638 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B6259139 : Blo 1156638 6259139 := bstep (se 1 (by rfl) ⟨4694354, by rfl⟩ : syracuseStep 6259139 = 9388709) B9388709
theorem B3572207 : Blo 1156638 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B2753023 : Blo 1156638 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B1737353 : Blo 1156638 1737353 := bstep (se 2 (by rfl) ⟨651507, by rfl⟩ : syracuseStep 1737353 = 1303015) B1303015
theorem B12518621 : Blo 1156638 12518621 := bstep (se 3 (by rfl) ⟨2347241, by rfl⟩ : syracuseStep 12518621 = 4694483) B4694483
theorem B54265565 : Blo 1156638 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B3967487 : Blo 1156638 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B1739759 : Blo 1156638 1739759 := bstep (se 1 (by rfl) ⟨1304819, by rfl⟩ : syracuseStep 1739759 = 2609639) B2609639
theorem B6261887 : Blo 1156638 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B1740059 : Blo 1156638 1740059 := bstep (se 1 (by rfl) ⟨1305044, by rfl⟩ : syracuseStep 1740059 = 2610089) B2610089
theorem B1740425 : Blo 1156638 1740425 := bstep (se 2 (by rfl) ⟨652659, by rfl⟩ : syracuseStep 1740425 = 1305319) B1305319
theorem B1740479 : Blo 1156638 1740479 := bstep (se 1 (by rfl) ⟨1305359, by rfl⟩ : syracuseStep 1740479 = 2610719) B2610719
theorem B1740527 : Blo 1156638 1740527 := bstep (se 1 (by rfl) ⟨1305395, by rfl⟩ : syracuseStep 1740527 = 2610791) B2610791
theorem B1740635 : Blo 1156638 1740635 := bstep (se 1 (by rfl) ⟨1305476, by rfl⟩ : syracuseStep 1740635 = 2610953) B2610953
theorem B1740647 : Blo 1156638 1740647 := bstep (se 1 (by rfl) ⟨1305485, by rfl⟩ : syracuseStep 1740647 = 2610971) B2610971
theorem B31657979 : Blo 1156638 31657979 := bstep (se 1 (by rfl) ⟨23743484, by rfl⟩ : syracuseStep 31657979 = 47486969) B47486969
theorem B5640367 : Blo 1156638 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B4396751 : Blo 1156638 4396751 := bstep (se 1 (by rfl) ⟨3297563, by rfl⟩ : syracuseStep 4396751 = 6595127) B6595127
theorem B26744687 : Blo 1156638 26744687 := bstep (se 1 (by rfl) ⟨20058515, by rfl⟩ : syracuseStep 26744687 = 40117031) B40117031
theorem B7411675 : Blo 1156638 7411675 := bstep (se 1 (by rfl) ⟨5558756, by rfl⟩ : syracuseStep 7411675 = 11117513) B11117513
theorem B26417423 : Blo 1156638 26417423 := bstep (se 1 (by rfl) ⟨19813067, by rfl⟩ : syracuseStep 26417423 = 39626135) B39626135
theorem B4398239 : Blo 1156638 4398239 := bstep (se 1 (by rfl) ⟨3298679, by rfl⟩ : syracuseStep 4398239 = 6597359) B6597359
theorem B6430033 : Blo 1156638 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B4399211 : Blo 1156638 4399211 := bstep (se 1 (by rfl) ⟨3299408, by rfl⟩ : syracuseStep 4399211 = 6598817) B6598817
theorem B13213853 : Blo 1156638 13213853 := bstep (se 3 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 13213853 = 4955195) B4955195
theorem B15835783 : Blo 1156638 15835783 := bstep (se 1 (by rfl) ⟨11876837, by rfl⟩ : syracuseStep 15835783 = 23753675) B23753675
theorem B6595901 : Blo 1156638 6595901 := bstep (se 3 (by rfl) ⟨1236731, by rfl⟩ : syracuseStep 6595901 = 2473463) B2473463
theorem B1157031 : Blo 1156638 1157031 := bstep (se 1 (by rfl) ⟨867773, by rfl⟩ : syracuseStep 1157031 = 1735547) B1735547
theorem B1157479 : Blo 1156638 1157479 := bstep (se 1 (by rfl) ⟨868109, by rfl⟩ : syracuseStep 1157479 = 1736219) B1736219
theorem B26716985 : Blo 1156638 26716985 := bstep (se 2 (by rfl) ⟨10018869, by rfl⟩ : syracuseStep 26716985 = 20037739) B20037739
theorem B126856115 : Blo 1156638 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B1650331 : Blo 1156638 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B481603643 : Blo 1156638 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B1159279 : Blo 1156638 1159279 := bstep (se 1 (by rfl) ⟨869459, by rfl⟩ : syracuseStep 1159279 = 1738919) B1738919
theorem B1159419 : Blo 1156638 1159419 := bstep (se 1 (by rfl) ⟨869564, by rfl⟩ : syracuseStep 1159419 = 1739129) B1739129
theorem B3911975 : Blo 1156638 3911975 := bstep (se 1 (by rfl) ⟨2933981, by rfl⟩ : syracuseStep 3911975 = 5867963) B5867963
theorem B9909161 : Blo 1156638 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B3912731 : Blo 1156638 3912731 := bstep (se 1 (by rfl) ⟨2934548, by rfl⟩ : syracuseStep 3912731 = 5869097) B5869097
theorem B3716219 : Blo 1156638 3716219 := bstep (se 1 (by rfl) ⟨2787164, by rfl⟩ : syracuseStep 3716219 = 5574329) B5574329
theorem B2930003 : Blo 1156638 2930003 := bstep (se 1 (by rfl) ⟨2197502, by rfl⟩ : syracuseStep 2930003 = 4395005) B4395005
theorem B29668841 : Blo 1156638 29668841 := bstep (se 2 (by rfl) ⟨11125815, by rfl⟩ : syracuseStep 29668841 = 22251631) B22251631
theorem B14824943 : Blo 1156638 14824943 := bstep (se 1 (by rfl) ⟨11118707, by rfl⟩ : syracuseStep 14824943 = 22237415) B22237415
theorem B2930195 : Blo 1156638 2930195 := bstep (se 1 (by rfl) ⟨2197646, by rfl⟩ : syracuseStep 2930195 = 4395293) B4395293
theorem B16725629 : Blo 1156638 16725629 := bstep (se 3 (by rfl) ⟨3136055, by rfl⟩ : syracuseStep 16725629 = 6272111) B6272111
theorem B6600527 : Blo 1156638 6600527 := bstep (se 1 (by rfl) ⟨4950395, by rfl⟩ : syracuseStep 6600527 = 9900791) B9900791
theorem B30062735 : Blo 1156638 30062735 := bstep (se 1 (by rfl) ⟨22547051, by rfl⟩ : syracuseStep 30062735 = 45094103) B45094103
theorem B3914783 : Blo 1156638 3914783 := bstep (se 1 (by rfl) ⟨2936087, by rfl⟩ : syracuseStep 3914783 = 5872175) B5872175
theorem B7421311 : Blo 1156638 7421311 := bstep (se 1 (by rfl) ⟨5565983, by rfl⟩ : syracuseStep 7421311 = 11131967) B11131967
theorem B228737783 : Blo 1156638 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B2606057 : Blo 1156638 2606057 := bstep (se 2 (by rfl) ⟨977271, by rfl⟩ : syracuseStep 2606057 = 1954543) B1954543
theorem B2606867 : Blo 1156638 2606867 := bstep (se 1 (by rfl) ⟨1955150, by rfl⟩ : syracuseStep 2606867 = 3910301) B3910301
theorem B5293993 : Blo 1156638 5293993 := bstep (se 2 (by rfl) ⟨1985247, by rfl⟩ : syracuseStep 5293993 = 3970495) B3970495
theorem B31673105 : Blo 1156638 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B3525535 : Blo 1156638 3525535 := bstep (se 1 (by rfl) ⟨2644151, by rfl⟩ : syracuseStep 3525535 = 5288303) B5288303
theorem B16698413 : Blo 1156638 16698413 := bstep (se 3 (by rfl) ⟨3130952, by rfl⟩ : syracuseStep 16698413 = 6261905) B6261905
theorem B2608289 : Blo 1156638 2608289 := bstep (se 2 (by rfl) ⟨978108, by rfl⟩ : syracuseStep 2608289 = 1956217) B1956217
theorem B2969579 : Blo 1156638 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B3133853 : Blo 1156638 3133853 := bstep (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) B1175195
theorem B2609711 : Blo 1156638 2609711 := bstep (se 1 (by rfl) ⟨1957283, by rfl⟩ : syracuseStep 2609711 = 3914567) B3914567
theorem B1954975 : Blo 1156638 1954975 := bstep (se 1 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 1954975 = 2932463) B2932463
theorem B31742057 : Blo 1156638 31742057 := bstep (se 2 (by rfl) ⟨11903271, by rfl⟩ : syracuseStep 31742057 = 23806543) B23806543
theorem B3135883 : Blo 1156638 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B9886333 : Blo 1156638 9886333 := bstep (se 3 (by rfl) ⟨1853687, by rfl⟩ : syracuseStep 9886333 = 3707375) B3707375
theorem B1235903 : Blo 1156638 1235903 := bstep (se 1 (by rfl) ⟨926927, by rfl⟩ : syracuseStep 1235903 = 1853855) B1853855
theorem B50126039 : Blo 1156638 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B162487781 : Blo 1156638 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B2350633 : Blo 1156638 2350633 := bstep (se 2 (by rfl) ⟨881487, by rfl⟩ : syracuseStep 2350633 = 1762975) B1762975
theorem B1302619 : Blo 1156638 1302619 := bstep (se 1 (by rfl) ⟨976964, by rfl⟩ : syracuseStep 1302619 = 1953929) B1953929
theorem B5857919 : Blo 1156638 5857919 := bstep (se 1 (by rfl) ⟨4393439, by rfl⟩ : syracuseStep 5857919 = 8786879) B8786879
theorem B9397403 : Blo 1156638 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B3302815 : Blo 1156638 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B13559663 : Blo 1156638 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B4942073 : Blo 1156638 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B23816567 : Blo 1156638 23816567 := bstep (se 1 (by rfl) ⟨17862425, by rfl⟩ : syracuseStep 23816567 = 35724851) B35724851
theorem B3762623 : Blo 1156638 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B3303919 : Blo 1156638 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B13200731 : Blo 1156638 13200731 := bstep (se 1 (by rfl) ⟨9900548, by rfl⟩ : syracuseStep 13200731 = 19801097) B19801097
theorem B5863103 : Blo 1156638 5863103 := bstep (se 1 (by rfl) ⟨4397327, by rfl⟩ : syracuseStep 5863103 = 8794655) B8794655
theorem B4946447 : Blo 1156638 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B23756561 : Blo 1156638 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B1736825 : Blo 1156638 1736825 := bstep (se 2 (by rfl) ⟨651309, by rfl⟩ : syracuseStep 1736825 = 1302619) B1302619
theorem B1737371 : Blo 1156638 1737371 := bstep (se 1 (by rfl) ⟨1303028, by rfl⟩ : syracuseStep 1737371 = 2606057) B2606057
theorem B3670697 : Blo 1156638 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B36177043 : Blo 1156638 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B1737911 : Blo 1156638 1737911 := bstep (se 1 (by rfl) ⟨1303433, by rfl⟩ : syracuseStep 1737911 = 2606867) B2606867
theorem B1738859 : Blo 1156638 1738859 := bstep (se 1 (by rfl) ⟨1304144, by rfl⟩ : syracuseStep 1738859 = 2608289) B2608289
theorem B1739807 : Blo 1156638 1739807 := bstep (se 1 (by rfl) ⟨1304855, by rfl⟩ : syracuseStep 1739807 = 2609711) B2609711
theorem B17829791 : Blo 1156638 17829791 := bstep (se 1 (by rfl) ⟨13372343, by rfl⟩ : syracuseStep 17829791 = 26744687) B26744687
theorem B44601677 : Blo 1156638 44601677 := bstep (se 3 (by rfl) ⟨8362814, by rfl⟩ : syracuseStep 44601677 = 16725629) B16725629
theorem B2200441 : Blo 1156638 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B3905279 : Blo 1156638 3905279 := bstep (se 1 (by rfl) ⟨2928959, by rfl⟩ : syracuseStep 3905279 = 5857919) B5857919
theorem B13178861 : Blo 1156638 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B6264935 : Blo 1156638 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B4397267 : Blo 1156638 4397267 := bstep (se 1 (by rfl) ⟨3297950, by rfl⟩ : syracuseStep 4397267 = 6595901) B6595901
theorem B321069095 : Blo 1156638 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B13181777 : Blo 1156638 13181777 := bstep (se 2 (by rfl) ⟨4943166, by rfl⟩ : syracuseStep 13181777 = 9886333) B9886333
theorem B3908735 : Blo 1156638 3908735 := bstep (se 1 (by rfl) ⟨2931551, by rfl⟩ : syracuseStep 3908735 = 5863103) B5863103
theorem B4400351 : Blo 1156638 4400351 := bstep (se 1 (by rfl) ⟨3300263, by rfl⟩ : syracuseStep 4400351 = 6600527) B6600527
theorem B15837707 : Blo 1156638 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B84421277 : Blo 1156638 84421277 := bstep (se 3 (by rfl) ⟨15828989, by rfl⟩ : syracuseStep 84421277 = 31657979) B31657979
theorem B1157871 : Blo 1156638 1157871 := bstep (se 1 (by rfl) ⟨868403, by rfl⟩ : syracuseStep 1157871 = 1736807) B1736807
theorem B4172759 : Blo 1156638 4172759 := bstep (se 1 (by rfl) ⟨3129569, by rfl⟩ : syracuseStep 4172759 = 6259139) B6259139
theorem B1158235 : Blo 1156638 1158235 := bstep (se 1 (by rfl) ⟨868676, by rfl⟩ : syracuseStep 1158235 = 1737353) B1737353
theorem B21114377 : Blo 1156638 21114377 := bstep (se 2 (by rfl) ⟨7917891, by rfl⟩ : syracuseStep 21114377 = 15835783) B15835783
theorem B21115403 : Blo 1156638 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B4403753 : Blo 1156638 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B1159839 : Blo 1156638 1159839 := bstep (se 1 (by rfl) ⟨869879, by rfl⟩ : syracuseStep 1159839 = 1739759) B1739759
theorem B4174591 : Blo 1156638 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1160039 : Blo 1156638 1160039 := bstep (se 1 (by rfl) ⟨870029, by rfl⟩ : syracuseStep 1160039 = 1740059) B1740059
theorem B1160283 : Blo 1156638 1160283 := bstep (se 1 (by rfl) ⟨870212, by rfl⟩ : syracuseStep 1160283 = 1740425) B1740425
theorem B1160319 : Blo 1156638 1160319 := bstep (se 1 (by rfl) ⟨870239, by rfl⟩ : syracuseStep 1160319 = 1740479) B1740479
theorem B1160351 : Blo 1156638 1160351 := bstep (se 1 (by rfl) ⟨870263, by rfl⟩ : syracuseStep 1160351 = 1740527) B1740527
theorem B7058657 : Blo 1156638 7058657 := bstep (se 2 (by rfl) ⟨2646996, by rfl⟩ : syracuseStep 7058657 = 5293993) B5293993
theorem B1160423 : Blo 1156638 1160423 := bstep (se 1 (by rfl) ⟨870317, by rfl⟩ : syracuseStep 1160423 = 1740635) B1740635
theorem B1160431 : Blo 1156638 1160431 := bstep (se 1 (by rfl) ⟨870323, by rfl⟩ : syracuseStep 1160431 = 1740647) B1740647
theorem B4405225 : Blo 1156638 4405225 := bstep (se 2 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 4405225 = 3303919) B3303919
theorem B2931167 : Blo 1156638 2931167 := bstep (se 1 (by rfl) ⟨2198375, by rfl⟩ : syracuseStep 2931167 = 4396751) B4396751
theorem B4700713 : Blo 1156638 4700713 := bstep (se 2 (by rfl) ⟨1762767, by rfl⟩ : syracuseStep 4700713 = 3525535) B3525535
theorem B17611615 : Blo 1156638 17611615 := bstep (se 1 (by rfl) ⟨13208711, by rfl⟩ : syracuseStep 17611615 = 26417423) B26417423
theorem B2932159 : Blo 1156638 2932159 := bstep (se 1 (by rfl) ⟨2199119, by rfl⟩ : syracuseStep 2932159 = 4398239) B4398239
theorem B2932807 : Blo 1156638 2932807 := bstep (se 1 (by rfl) ⟨2199605, by rfl⟩ : syracuseStep 2932807 = 4399211) B4399211
theorem B7520489 : Blo 1156638 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B13190525 : Blo 1156638 13190525 := bstep (se 3 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 13190525 = 4946447) B4946447
theorem B2606633 : Blo 1156638 2606633 := bstep (se 2 (by rfl) ⟨977487, by rfl⟩ : syracuseStep 2606633 = 1954975) B1954975
theorem B15877711 : Blo 1156638 15877711 := bstep (se 1 (by rfl) ⟨11908283, by rfl⟩ : syracuseStep 15877711 = 23816567) B23816567
theorem B2508415 : Blo 1156638 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B17811323 : Blo 1156638 17811323 := bstep (se 1 (by rfl) ⟨13358492, by rfl⟩ : syracuseStep 17811323 = 26716985) B26716985
theorem B8800487 : Blo 1156638 8800487 := bstep (se 1 (by rfl) ⟨6600365, by rfl⟩ : syracuseStep 8800487 = 13200731) B13200731
theorem B3295741 : Blo 1156638 3295741 := bstep (se 3 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 3295741 = 1235903) B1235903
theorem B9882233 : Blo 1156638 9882233 := bstep (se 2 (by rfl) ⟨3705837, by rfl⟩ : syracuseStep 9882233 = 7411675) B7411675
theorem B2607983 : Blo 1156638 2607983 := bstep (se 1 (by rfl) ⟨1955987, by rfl⟩ : syracuseStep 2607983 = 3911975) B3911975
theorem B4181177 : Blo 1156638 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B6606107 : Blo 1156638 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B2608487 : Blo 1156638 2608487 := bstep (se 1 (by rfl) ⟨1956365, by rfl⟩ : syracuseStep 2608487 = 3912731) B3912731
theorem B2477479 : Blo 1156638 2477479 := bstep (se 1 (by rfl) ⟨1858109, by rfl⟩ : syracuseStep 2477479 = 3716219) B3716219
theorem B1953335 : Blo 1156638 1953335 := bstep (se 1 (by rfl) ⟨1465001, by rfl⟩ : syracuseStep 1953335 = 2930003) B2930003
theorem B19779227 : Blo 1156638 19779227 := bstep (se 1 (by rfl) ⟨14834420, by rfl⟩ : syracuseStep 19779227 = 29668841) B29668841
theorem B9883295 : Blo 1156638 9883295 := bstep (se 1 (by rfl) ⟨7412471, by rfl⟩ : syracuseStep 9883295 = 14824943) B14824943
theorem B1953463 : Blo 1156638 1953463 := bstep (se 1 (by rfl) ⟨1465097, by rfl⟩ : syracuseStep 1953463 = 2930195) B2930195
theorem B20041823 : Blo 1156638 20041823 := bstep (se 1 (by rfl) ⟨15031367, by rfl⟩ : syracuseStep 20041823 = 30062735) B30062735
theorem B8573377 : Blo 1156638 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B2609855 : Blo 1156638 2609855 := bstep (se 1 (by rfl) ⟨1957391, by rfl⟩ : syracuseStep 2609855 = 3914783) B3914783
theorem B3134177 : Blo 1156638 3134177 := bstep (se 2 (by rfl) ⟨1175316, by rfl⟩ : syracuseStep 3134177 = 2350633) B2350633
theorem B7918877 : Blo 1156638 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B3298907 : Blo 1156638 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B2381471 : Blo 1156638 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B152491855 : Blo 1156638 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B8345747 : Blo 1156638 8345747 := bstep (se 1 (by rfl) ⟨6259310, by rfl⟩ : syracuseStep 8345747 = 12518621) B12518621
theorem B2644991 : Blo 1156638 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B11132275 : Blo 1156638 11132275 := bstep (se 1 (by rfl) ⟨8349206, by rfl⟩ : syracuseStep 11132275 = 16698413) B16698413
theorem B2089235 : Blo 1156638 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B21161371 : Blo 1156638 21161371 := bstep (se 1 (by rfl) ⟨15871028, by rfl⟩ : syracuseStep 21161371 = 31742057) B31742057
theorem B33417359 : Blo 1156638 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B108325187 : Blo 1156638 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B8809235 : Blo 1156638 8809235 := bstep (se 1 (by rfl) ⟨6606926, by rfl⟩ : syracuseStep 8809235 = 13213853) B13213853
theorem B9039775 : Blo 1156638 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B84570743 : Blo 1156638 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B9895081 : Blo 1156638 9895081 := bstep (se 2 (by rfl) ⟨3710655, by rfl⟩ : syracuseStep 9895081 = 7421311) B7421311
theorem B5013659 : Blo 1156638 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B1737755 : Blo 1156638 1737755 := bstep (se 1 (by rfl) ⟨1303316, by rfl⟩ : syracuseStep 1737755 = 2606633) B2606633
theorem B5866991 : Blo 1156638 5866991 := bstep (se 1 (by rfl) ⟨4400243, by rfl⟩ : syracuseStep 5866991 = 8800487) B8800487
theorem B48236057 : Blo 1156638 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B6588155 : Blo 1156638 6588155 := bstep (se 1 (by rfl) ⟨4941116, by rfl⟩ : syracuseStep 6588155 = 9882233) B9882233
theorem B28215161 : Blo 1156638 28215161 := bstep (se 2 (by rfl) ⟨10580685, by rfl⟩ : syracuseStep 28215161 = 21161371) B21161371
theorem B1738655 : Blo 1156638 1738655 := bstep (se 1 (by rfl) ⟨1303991, by rfl⟩ : syracuseStep 1738655 = 2607983) B2607983
theorem B21170281 : Blo 1156638 21170281 := bstep (se 2 (by rfl) ⟨7938855, by rfl⟩ : syracuseStep 21170281 = 15877711) B15877711
theorem B1738991 : Blo 1156638 1738991 := bstep (se 1 (by rfl) ⟨1304243, by rfl⟩ : syracuseStep 1738991 = 2608487) B2608487
theorem B6588863 : Blo 1156638 6588863 := bstep (se 1 (by rfl) ⟨4941647, by rfl⟩ : syracuseStep 6588863 = 9883295) B9883295
theorem B1739903 : Blo 1156638 1739903 := bstep (se 1 (by rfl) ⟨1304927, by rfl⟩ : syracuseStep 1739903 = 2609855) B2609855
theorem B4394321 : Blo 1156638 4394321 := bstep (se 2 (by rfl) ⟨1647870, by rfl⟩ : syracuseStep 4394321 = 3295741) B3295741
theorem B5279251 : Blo 1156638 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B8785907 : Blo 1156638 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B214046063 : Blo 1156638 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B8787851 : Blo 1156638 8787851 := bstep (se 1 (by rfl) ⟨6590888, by rfl⟩ : syracuseStep 8787851 = 13181777) B13181777
theorem B10558471 : Blo 1156638 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B5872823 : Blo 1156638 5872823 := bstep (se 1 (by rfl) ⟨4404617, by rfl⟩ : syracuseStep 5872823 = 8809235) B8809235
theorem B5873633 : Blo 1156638 5873633 := bstep (se 2 (by rfl) ⟨2202612, by rfl⟩ : syracuseStep 5873633 = 4405225) B4405225
theorem B11149805 : Blo 1156638 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B13378213 : Blo 1156638 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B6267617 : Blo 1156638 6267617 := bstep (se 2 (by rfl) ⟨2350356, by rfl⟩ : syracuseStep 6267617 = 4700713) B4700713
theorem B3909545 : Blo 1156638 3909545 := bstep (se 2 (by rfl) ⟨1466079, by rfl⟩ : syracuseStep 3909545 = 2932159) B2932159
theorem B1157883 : Blo 1156638 1157883 := bstep (se 1 (by rfl) ⟨868412, by rfl⟩ : syracuseStep 1157883 = 1736825) B1736825
theorem B3910409 : Blo 1156638 3910409 := bstep (se 2 (by rfl) ⟨1466403, by rfl⟩ : syracuseStep 3910409 = 2932807) B2932807
theorem B1158247 : Blo 1156638 1158247 := bstep (se 1 (by rfl) ⟨868685, by rfl⟩ : syracuseStep 1158247 = 1737371) B1737371
theorem B1158607 : Blo 1156638 1158607 := bstep (se 1 (by rfl) ⟨868955, by rfl⟩ : syracuseStep 1158607 = 1737911) B1737911
theorem B8793683 : Blo 1156638 8793683 := bstep (se 1 (by rfl) ⟨6595262, by rfl⟩ : syracuseStep 8793683 = 13190525) B13190525
theorem B11874215 : Blo 1156638 11874215 := bstep (se 1 (by rfl) ⟨8905661, by rfl⟩ : syracuseStep 11874215 = 17811323) B17811323
theorem B1159239 : Blo 1156638 1159239 := bstep (se 1 (by rfl) ⟨869429, by rfl⟩ : syracuseStep 1159239 = 1738859) B1738859
theorem B1159871 : Blo 1156638 1159871 := bstep (se 1 (by rfl) ⟨869903, by rfl⟩ : syracuseStep 1159871 = 1739807) B1739807
theorem B4404071 : Blo 1156638 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B13186151 : Blo 1156638 13186151 := bstep (se 1 (by rfl) ⟨9889613, by rfl⟩ : syracuseStep 13186151 = 19779227) B19779227
theorem B29734451 : Blo 1156638 29734451 := bstep (se 1 (by rfl) ⟨22300838, by rfl⟩ : syracuseStep 29734451 = 44601677) B44601677
theorem B1587647 : Blo 1156638 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B2603519 : Blo 1156638 2603519 := bstep (se 1 (by rfl) ⟨1952639, by rfl⟩ : syracuseStep 2603519 = 3905279) B3905279
theorem B4176623 : Blo 1156638 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B2931511 : Blo 1156638 2931511 := bstep (se 1 (by rfl) ⟨2198633, by rfl⟩ : syracuseStep 2931511 = 4397267) B4397267
theorem B8797085 : Blo 1156638 8797085 := bstep (se 3 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 8797085 = 3298907) B3298907
theorem B2604617 : Blo 1156638 2604617 := bstep (se 2 (by rfl) ⟨976731, by rfl⟩ : syracuseStep 2604617 = 1953463) B1953463
theorem B1392823 : Blo 1156638 1392823 := bstep (se 1 (by rfl) ⟨1044617, by rfl⟩ : syracuseStep 1392823 = 2089235) B2089235
theorem B2605823 : Blo 1156638 2605823 := bstep (se 1 (by rfl) ⟨1954367, by rfl⟩ : syracuseStep 2605823 = 3908735) B3908735
theorem B2933567 : Blo 1156638 2933567 := bstep (se 1 (by rfl) ⟨2200175, by rfl⟩ : syracuseStep 2933567 = 4400351) B4400351
theorem B2933921 : Blo 1156638 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B56280851 : Blo 1156638 56280851 := bstep (se 1 (by rfl) ⟨42210638, by rfl⟩ : syracuseStep 56280851 = 84421277) B84421277
theorem B14076251 : Blo 1156638 14076251 := bstep (se 1 (by rfl) ⟨10557188, by rfl⟩ : syracuseStep 14076251 = 21114377) B21114377
theorem B14076935 : Blo 1156638 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B2935835 : Blo 1156638 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B56380495 : Blo 1156638 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B4705771 : Blo 1156638 4705771 := bstep (se 1 (by rfl) ⟨3529328, by rfl⟩ : syracuseStep 4705771 = 7058657) B7058657
theorem B23482153 : Blo 1156638 23482153 := bstep (se 2 (by rfl) ⟨8805807, by rfl⟩ : syracuseStep 23482153 = 17611615) B17611615
theorem B13193441 : Blo 1156638 13193441 := bstep (se 2 (by rfl) ⟨4947540, by rfl⟩ : syracuseStep 13193441 = 9895081) B9895081
theorem B1954111 : Blo 1156638 1954111 := bstep (se 1 (by rfl) ⟨1465583, by rfl⟩ : syracuseStep 1954111 = 2931167) B2931167
theorem B9788525 : Blo 1156638 9788525 := bstep (se 3 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 9788525 = 3670697) B3670697
theorem B1302223 : Blo 1156638 1302223 := bstep (se 1 (by rfl) ⟨976667, by rfl⟩ : syracuseStep 1302223 = 1953335) B1953335
theorem B11886527 : Blo 1156638 11886527 := bstep (se 1 (by rfl) ⟨8914895, by rfl⟩ : syracuseStep 11886527 = 17829791) B17829791
theorem B13361215 : Blo 1156638 13361215 := bstep (se 1 (by rfl) ⟨10020911, by rfl⟩ : syracuseStep 13361215 = 20041823) B20041823
theorem B2089451 : Blo 1156638 2089451 := bstep (se 1 (by rfl) ⟨1567088, by rfl⟩ : syracuseStep 2089451 = 3134177) B3134177
theorem B5563831 : Blo 1156638 5563831 := bstep (se 1 (by rfl) ⟨4172873, by rfl⟩ : syracuseStep 5563831 = 8345747) B8345747
theorem B3303305 : Blo 1156638 3303305 := bstep (se 2 (by rfl) ⟨1238739, by rfl⟩ : syracuseStep 3303305 = 2477479) B2477479
theorem B1763327 : Blo 1156638 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B12053033 : Blo 1156638 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B11431169 : Blo 1156638 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B5566121 : Blo 1156638 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B22278239 : Blo 1156638 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B72216791 : Blo 1156638 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B2781839 : Blo 1156638 2781839 := bstep (se 1 (by rfl) ⟨2086379, by rfl⟩ : syracuseStep 2781839 = 4172759) B4172759
theorem B203322473 : Blo 1156638 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B14843033 : Blo 1156638 14843033 := bstep (se 2 (by rfl) ⟨5566137, by rfl⟩ : syracuseStep 14843033 = 11132275) B11132275
theorem B3342439 : Blo 1156638 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B1737215 : Blo 1156638 1737215 := bstep (se 1 (by rfl) ⟨1302911, by rfl⟩ : syracuseStep 1737215 = 2605823) B2605823
theorem B4392103 : Blo 1156638 4392103 := bstep (se 1 (by rfl) ⟨3294077, by rfl⟩ : syracuseStep 4392103 = 6588155) B6588155
theorem B37520567 : Blo 1156638 37520567 := bstep (se 1 (by rfl) ⟨28140425, by rfl⟩ : syracuseStep 37520567 = 56280851) B56280851
theorem B18810107 : Blo 1156638 18810107 := bstep (se 1 (by rfl) ⟨14107580, by rfl⟩ : syracuseStep 18810107 = 28215161) B28215161
theorem B4392575 : Blo 1156638 4392575 := bstep (se 1 (by rfl) ⟨3294431, by rfl⟩ : syracuseStep 4392575 = 6588863) B6588863
theorem B75173993 : Blo 1156638 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B6525683 : Blo 1156638 6525683 := bstep (se 1 (by rfl) ⟨4894262, by rfl⟩ : syracuseStep 6525683 = 9788525) B9788525
theorem B4233725 : Blo 1156638 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B2202203 : Blo 1156638 2202203 := bstep (se 1 (by rfl) ⟨1651652, by rfl⟩ : syracuseStep 2202203 = 3303305) B3303305
theorem B8035355 : Blo 1156638 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B3710747 : Blo 1156638 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B14852159 : Blo 1156638 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B48144527 : Blo 1156638 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B8790767 : Blo 1156638 8790767 := bstep (se 1 (by rfl) ⟨6593075, by rfl⟩ : syracuseStep 8790767 = 13186151) B13186151
theorem B3908681 : Blo 1156638 3908681 := bstep (se 2 (by rfl) ⟨1465755, by rfl⟩ : syracuseStep 3908681 = 2931511) B2931511
theorem B1158503 : Blo 1156638 1158503 := bstep (se 1 (by rfl) ⟨868877, by rfl⟩ : syracuseStep 1158503 = 1737755) B1737755
theorem B17837617 : Blo 1156638 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B3911327 : Blo 1156638 3911327 := bstep (se 1 (by rfl) ⟨2933495, by rfl⟩ : syracuseStep 3911327 = 5866991) B5866991
theorem B32157371 : Blo 1156638 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B1159103 : Blo 1156638 1159103 := bstep (se 1 (by rfl) ⟨869327, by rfl⟩ : syracuseStep 1159103 = 1738655) B1738655
theorem B1159327 : Blo 1156638 1159327 := bstep (se 1 (by rfl) ⟨869495, by rfl⟩ : syracuseStep 1159327 = 1738991) B1738991
theorem B9384167 : Blo 1156638 9384167 := bstep (se 1 (by rfl) ⟨7038125, by rfl⟩ : syracuseStep 9384167 = 14076251) B14076251
theorem B7418441 : Blo 1156638 7418441 := bstep (se 2 (by rfl) ⟨2781915, by rfl⟩ : syracuseStep 7418441 = 5563831) B5563831
theorem B9384623 : Blo 1156638 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B1159935 : Blo 1156638 1159935 := bstep (se 1 (by rfl) ⟨869951, by rfl⟩ : syracuseStep 1159935 = 1739903) B1739903
theorem B2929547 : Blo 1156638 2929547 := bstep (se 1 (by rfl) ⟨2197160, by rfl⟩ : syracuseStep 2929547 = 4394321) B4394321
theorem B28227041 : Blo 1156638 28227041 := bstep (se 2 (by rfl) ⟨10585140, by rfl⟩ : syracuseStep 28227041 = 21170281) B21170281
theorem B8795627 : Blo 1156638 8795627 := bstep (se 1 (by rfl) ⟨6596720, by rfl⟩ : syracuseStep 8795627 = 13193441) B13193441
theorem B6274361 : Blo 1156638 6274361 := bstep (se 2 (by rfl) ⟨2352885, by rfl⟩ : syracuseStep 6274361 = 4705771) B4705771
theorem B3915215 : Blo 1156638 3915215 := bstep (se 1 (by rfl) ⟨2936411, by rfl⟩ : syracuseStep 3915215 = 5872823) B5872823
theorem B31309537 : Blo 1156638 31309537 := bstep (se 2 (by rfl) ⟨11741076, by rfl⟩ : syracuseStep 31309537 = 23482153) B23482153
theorem B3915755 : Blo 1156638 3915755 := bstep (se 1 (by rfl) ⟨2936816, by rfl⟩ : syracuseStep 3915755 = 5873633) B5873633
theorem B4702205 : Blo 1156638 4702205 := bstep (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) B1763327
theorem B1392967 : Blo 1156638 1392967 := bstep (se 1 (by rfl) ⟨1044725, by rfl⟩ : syracuseStep 1392967 = 2089451) B2089451
theorem B2605481 : Blo 1156638 2605481 := bstep (se 2 (by rfl) ⟨977055, by rfl⟩ : syracuseStep 2605481 = 1954111) B1954111
theorem B4178411 : Blo 1156638 4178411 := bstep (se 1 (by rfl) ⟨3133808, by rfl⟩ : syracuseStep 4178411 = 6267617) B6267617
theorem B2606363 : Blo 1156638 2606363 := bstep (se 1 (by rfl) ⟨1954772, by rfl⟩ : syracuseStep 2606363 = 3909545) B3909545
theorem B2606939 : Blo 1156638 2606939 := bstep (se 1 (by rfl) ⟨1955204, by rfl⟩ : syracuseStep 2606939 = 3910409) B3910409
theorem B7620779 : Blo 1156638 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B7916143 : Blo 1156638 7916143 := bstep (se 1 (by rfl) ⟨5937107, by rfl⟩ : syracuseStep 7916143 = 11874215) B11874215
theorem B1854559 : Blo 1156638 1854559 := bstep (se 1 (by rfl) ⟨1390919, by rfl⟩ : syracuseStep 1854559 = 2781839) B2781839
theorem B2936047 : Blo 1156638 2936047 := bstep (se 1 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 2936047 = 4404071) B4404071
theorem B135548315 : Blo 1156638 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B14077961 : Blo 1156638 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B17814953 : Blo 1156638 17814953 := bstep (se 2 (by rfl) ⟨6680607, by rfl⟩ : syracuseStep 17814953 = 13361215) B13361215
theorem B1857097 : Blo 1156638 1857097 := bstep (se 2 (by rfl) ⟨696411, by rfl⟩ : syracuseStep 1857097 = 1392823) B1392823
theorem B1955711 : Blo 1156638 1955711 := bstep (se 1 (by rfl) ⟨1466783, by rfl⟩ : syracuseStep 1955711 = 2933567) B2933567
theorem B1955947 : Blo 1156638 1955947 := bstep (se 1 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 1955947 = 2933921) B2933921
theorem B1957223 : Blo 1156638 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B5857271 : Blo 1156638 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B142697375 : Blo 1156638 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B5858567 : Blo 1156638 5858567 := bstep (se 1 (by rfl) ⟨4393925, by rfl⟩ : syracuseStep 5858567 = 8787851) B8787851
theorem B7039001 : Blo 1156638 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B7924351 : Blo 1156638 7924351 := bstep (se 1 (by rfl) ⟨5943263, by rfl⟩ : syracuseStep 7924351 = 11886527) B11886527
theorem B7433203 : Blo 1156638 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B11137661 : Blo 1156638 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B5862455 : Blo 1156638 5862455 := bstep (se 1 (by rfl) ⟨4396841, by rfl⟩ : syracuseStep 5862455 = 8793683) B8793683
theorem B19822967 : Blo 1156638 19822967 := bstep (se 1 (by rfl) ⟨14867225, by rfl⟩ : syracuseStep 19822967 = 29734451) B29734451
theorem B1735679 : Blo 1156638 1735679 := bstep (se 1 (by rfl) ⟨1301759, by rfl⟩ : syracuseStep 1735679 = 2603519) B2603519
theorem B5864723 : Blo 1156638 5864723 := bstep (se 1 (by rfl) ⟨4398542, by rfl⟩ : syracuseStep 5864723 = 8797085) B8797085
theorem B9895355 : Blo 1156638 9895355 := bstep (se 1 (by rfl) ⟨7421516, by rfl⟩ : syracuseStep 9895355 = 14843033) B14843033
theorem B1736297 : Blo 1156638 1736297 := bstep (se 2 (by rfl) ⟨651111, by rfl⟩ : syracuseStep 1736297 = 1302223) B1302223
theorem B1736411 : Blo 1156638 1736411 := bstep (se 1 (by rfl) ⟨1302308, by rfl⟩ : syracuseStep 1736411 = 2604617) B2604617
theorem B4456585 : Blo 1156638 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B1736987 : Blo 1156638 1736987 := bstep (se 1 (by rfl) ⟨1302740, by rfl⟩ : syracuseStep 1736987 = 2605481) B2605481
theorem B2785607 : Blo 1156638 2785607 := bstep (se 1 (by rfl) ⟨2089205, by rfl⟩ : syracuseStep 2785607 = 4178411) B4178411
theorem B1737575 : Blo 1156638 1737575 := bstep (se 1 (by rfl) ⟨1303181, by rfl⟩ : syracuseStep 1737575 = 2606363) B2606363
theorem B1737959 : Blo 1156638 1737959 := bstep (se 1 (by rfl) ⟨1303469, by rfl⟩ : syracuseStep 1737959 = 2606939) B2606939
theorem B5080519 : Blo 1156638 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B10554857 : Blo 1156638 10554857 := bstep (se 2 (by rfl) ⟨3958071, by rfl⟩ : syracuseStep 10554857 = 7916143) B7916143
theorem B2822483 : Blo 1156638 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B3904847 : Blo 1156638 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B9901439 : Blo 1156638 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B95131583 : Blo 1156638 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B3905711 : Blo 1156638 3905711 := bstep (se 1 (by rfl) ⟨2929283, by rfl⟩ : syracuseStep 3905711 = 5858567) B5858567
theorem B4692667 : Blo 1156638 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B3908303 : Blo 1156638 3908303 := bstep (se 1 (by rfl) ⟨2931227, by rfl⟩ : syracuseStep 3908303 = 5862455) B5862455
theorem B18818027 : Blo 1156638 18818027 := bstep (se 1 (by rfl) ⟨14113520, by rfl⟩ : syracuseStep 18818027 = 28227041) B28227041
theorem B13215311 : Blo 1156638 13215311 := bstep (se 1 (by rfl) ⟨9911483, by rfl⟩ : syracuseStep 13215311 = 19822967) B19822967
theorem B1157119 : Blo 1156638 1157119 := bstep (se 1 (by rfl) ⟨867839, by rfl⟩ : syracuseStep 1157119 = 1735679) B1735679
theorem B3909815 : Blo 1156638 3909815 := bstep (se 1 (by rfl) ⟨2932361, by rfl⟩ : syracuseStep 3909815 = 5864723) B5864723
theorem B6596903 : Blo 1156638 6596903 := bstep (se 1 (by rfl) ⟨4947677, by rfl⟩ : syracuseStep 6596903 = 9895355) B9895355
theorem B1157531 : Blo 1156638 1157531 := bstep (se 1 (by rfl) ⟨868148, by rfl⟩ : syracuseStep 1157531 = 1736297) B1736297
theorem B1157607 : Blo 1156638 1157607 := bstep (se 1 (by rfl) ⟨868205, by rfl⟩ : syracuseStep 1157607 = 1736411) B1736411
theorem B1158143 : Blo 1156638 1158143 := bstep (se 1 (by rfl) ⟨868607, by rfl⟩ : syracuseStep 1158143 = 1737215) B1737215
theorem B25013711 : Blo 1156638 25013711 := bstep (se 1 (by rfl) ⟨18760283, by rfl⟩ : syracuseStep 25013711 = 37520567) B37520567
theorem B2928383 : Blo 1156638 2928383 := bstep (se 1 (by rfl) ⟨2196287, by rfl⟩ : syracuseStep 2928383 = 4392575) B4392575
theorem B9385307 : Blo 1156638 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B50115995 : Blo 1156638 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B10565801 : Blo 1156638 10565801 := bstep (se 2 (by rfl) ⟨3962175, by rfl⟩ : syracuseStep 10565801 = 7924351) B7924351
theorem B11876635 : Blo 1156638 11876635 := bstep (se 1 (by rfl) ⟨8907476, by rfl⟩ : syracuseStep 11876635 = 17814953) B17814953
theorem B9910937 : Blo 1156638 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B3914729 : Blo 1156638 3914729 := bstep (se 2 (by rfl) ⟨1468023, by rfl⟩ : syracuseStep 3914729 = 2936047) B2936047
theorem B5356903 : Blo 1156638 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B2473831 : Blo 1156638 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B32096351 : Blo 1156638 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B2605787 : Blo 1156638 2605787 := bstep (se 1 (by rfl) ⟨1954340, by rfl⟩ : syracuseStep 2605787 = 3908681) B3908681
theorem B2476129 : Blo 1156638 2476129 := bstep (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) B1857097
theorem B2607551 : Blo 1156638 2607551 := bstep (se 1 (by rfl) ⟨1955663, by rfl⟩ : syracuseStep 2607551 = 3911327) B3911327
theorem B2607929 : Blo 1156638 2607929 := bstep (se 2 (by rfl) ⟨977973, by rfl⟩ : syracuseStep 2607929 = 1955947) B1955947
theorem B7425107 : Blo 1156638 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B1953031 : Blo 1156638 1953031 := bstep (se 1 (by rfl) ⟨1464773, by rfl⟩ : syracuseStep 1953031 = 2929547) B2929547
theorem B16731629 : Blo 1156638 16731629 := bstep (se 3 (by rfl) ⟨3137180, by rfl⟩ : syracuseStep 16731629 = 6274361) B6274361
theorem B2610143 : Blo 1156638 2610143 := bstep (se 1 (by rfl) ⟨1957607, by rfl⟩ : syracuseStep 2610143 = 3915215) B3915215
theorem B2610503 : Blo 1156638 2610503 := bstep (se 1 (by rfl) ⟨1957877, by rfl⟩ : syracuseStep 2610503 = 3915755) B3915755
theorem B3134803 : Blo 1156638 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B12540071 : Blo 1156638 12540071 := bstep (se 1 (by rfl) ⟨9405053, by rfl⟩ : syracuseStep 12540071 = 18810107) B18810107
theorem B5856137 : Blo 1156638 5856137 := bstep (se 2 (by rfl) ⟨2196051, by rfl⟩ : syracuseStep 5856137 = 4392103) B4392103
theorem B7429157 : Blo 1156638 7429157 := bstep (se 4 (by rfl) ⟨696483, by rfl⟩ : syracuseStep 7429157 = 1392967) B1392967
theorem B90365543 : Blo 1156638 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B4350455 : Blo 1156638 4350455 := bstep (se 1 (by rfl) ⟨3262841, by rfl⟩ : syracuseStep 4350455 = 6525683) B6525683
theorem B1303807 : Blo 1156638 1303807 := bstep (se 1 (by rfl) ⟨977855, by rfl⟩ : syracuseStep 1303807 = 1955711) B1955711
theorem B1468135 : Blo 1156638 1468135 := bstep (se 1 (by rfl) ⟨1101101, by rfl⟩ : syracuseStep 1468135 = 2202203) B2202203
theorem B23783489 : Blo 1156638 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B1304815 : Blo 1156638 1304815 := bstep (se 1 (by rfl) ⟨978611, by rfl⟩ : syracuseStep 1304815 = 1957223) B1957223
theorem B5860511 : Blo 1156638 5860511 := bstep (se 1 (by rfl) ⟨4395383, by rfl⟩ : syracuseStep 5860511 = 8790767) B8790767
theorem B9890981 : Blo 1156638 9890981 := bstep (se 4 (by rfl) ⟨927279, by rfl⟩ : syracuseStep 9890981 = 1854559) B1854559
theorem B6256111 : Blo 1156638 6256111 := bstep (se 1 (by rfl) ⟨4692083, by rfl⟩ : syracuseStep 6256111 = 9384167) B9384167
theorem B4945627 : Blo 1156638 4945627 := bstep (se 1 (by rfl) ⟨3709220, by rfl⟩ : syracuseStep 4945627 = 7418441) B7418441
theorem B6256415 : Blo 1156638 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B5863751 : Blo 1156638 5863751 := bstep (se 1 (by rfl) ⟨4397813, by rfl⟩ : syracuseStep 5863751 = 8795627) B8795627
theorem B85752989 : Blo 1156638 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B41746049 : Blo 1156638 41746049 := bstep (se 2 (by rfl) ⟨15654768, by rfl⟩ : syracuseStep 41746049 = 31309537) B31309537
theorem B21397567 : Blo 1156638 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B1737191 : Blo 1156638 1737191 := bstep (se 1 (by rfl) ⟨1302893, by rfl⟩ : syracuseStep 1737191 = 2605787) B2605787
theorem B1738367 : Blo 1156638 1738367 := bstep (se 1 (by rfl) ⟨1303775, by rfl⟩ : syracuseStep 1738367 = 2607551) B2607551
theorem B1738409 : Blo 1156638 1738409 := bstep (se 2 (by rfl) ⟨651903, by rfl⟩ : syracuseStep 1738409 = 1303807) B1303807
theorem B1738619 : Blo 1156638 1738619 := bstep (se 1 (by rfl) ⟨1303964, by rfl⟩ : syracuseStep 1738619 = 2607929) B2607929
theorem B4950071 : Blo 1156638 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B1739753 : Blo 1156638 1739753 := bstep (se 2 (by rfl) ⟨652407, by rfl⟩ : syracuseStep 1739753 = 1304815) B1304815
theorem B1740095 : Blo 1156638 1740095 := bstep (se 1 (by rfl) ⟨1305071, by rfl⟩ : syracuseStep 1740095 = 2610143) B2610143
theorem B1740335 : Blo 1156638 1740335 := bstep (se 1 (by rfl) ⟨1305251, by rfl⟩ : syracuseStep 1740335 = 2610503) B2610503
theorem B8360047 : Blo 1156638 8360047 := bstep (se 1 (by rfl) ⟨6270035, by rfl⟩ : syracuseStep 8360047 = 12540071) B12540071
theorem B3904091 : Blo 1156638 3904091 := bstep (se 1 (by rfl) ⟨2928068, by rfl⟩ : syracuseStep 3904091 = 5856137) B5856137
theorem B4952771 : Blo 1156638 4952771 := bstep (se 1 (by rfl) ⟨3714578, by rfl⟩ : syracuseStep 4952771 = 7429157) B7429157
theorem B4397935 : Blo 1156638 4397935 := bstep (se 1 (by rfl) ⟨3298451, by rfl⟩ : syracuseStep 4397935 = 6596903) B6596903
theorem B3907007 : Blo 1156638 3907007 := bstep (se 1 (by rfl) ⟨2930255, by rfl⟩ : syracuseStep 3907007 = 5860511) B5860511
theorem B6593987 : Blo 1156638 6593987 := bstep (se 1 (by rfl) ⟨4945490, by rfl⟩ : syracuseStep 6593987 = 9890981) B9890981
theorem B6594169 : Blo 1156638 6594169 := bstep (se 2 (by rfl) ⟨2472813, by rfl⟩ : syracuseStep 6594169 = 4945627) B4945627
theorem B15835513 : Blo 1156638 15835513 := bstep (se 2 (by rfl) ⟨5938317, by rfl⟩ : syracuseStep 15835513 = 11876635) B11876635
theorem B4170943 : Blo 1156638 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B3909167 : Blo 1156638 3909167 := bstep (se 1 (by rfl) ⟨2931875, by rfl⟩ : syracuseStep 3909167 = 5863751) B5863751
theorem B27830699 : Blo 1156638 27830699 := bstep (se 1 (by rfl) ⟨20873024, by rfl⟩ : syracuseStep 27830699 = 41746049) B41746049
theorem B1157991 : Blo 1156638 1157991 := bstep (se 1 (by rfl) ⟨868493, by rfl⟩ : syracuseStep 1157991 = 1736987) B1736987
theorem B1158383 : Blo 1156638 1158383 := bstep (se 1 (by rfl) ⟨868787, by rfl⟩ : syracuseStep 1158383 = 1737575) B1737575
theorem B23768453 : Blo 1156638 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B1158639 : Blo 1156638 1158639 := bstep (se 1 (by rfl) ⟨868979, by rfl⟩ : syracuseStep 1158639 = 1737959) B1737959
theorem B11154419 : Blo 1156638 11154419 := bstep (se 1 (by rfl) ⟨8365814, by rfl⟩ : syracuseStep 11154419 = 16731629) B16731629
theorem B2603231 : Blo 1156638 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B6600959 : Blo 1156638 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B63421055 : Blo 1156638 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B2603807 : Blo 1156638 2603807 := bstep (se 1 (by rfl) ⟨1952855, by rfl⟩ : syracuseStep 2603807 = 3905711) B3905711
theorem B2604041 : Blo 1156638 2604041 := bstep (se 2 (by rfl) ⟨976515, by rfl⟩ : syracuseStep 2604041 = 1953031) B1953031
theorem B60243695 : Blo 1156638 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B2900303 : Blo 1156638 2900303 := bstep (se 1 (by rfl) ⟨2175227, by rfl⟩ : syracuseStep 2900303 = 4350455) B4350455
theorem B2605535 : Blo 1156638 2605535 := bstep (se 1 (by rfl) ⟨1954151, by rfl⟩ : syracuseStep 2605535 = 3908303) B3908303
theorem B2606543 : Blo 1156638 2606543 := bstep (se 1 (by rfl) ⟨1954907, by rfl⟩ : syracuseStep 2606543 = 3909815) B3909815
theorem B4179737 : Blo 1156638 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B8341481 : Blo 1156638 8341481 := bstep (se 2 (by rfl) ⟨3128055, by rfl⟩ : syracuseStep 8341481 = 6256111) B6256111
theorem B1952255 : Blo 1156638 1952255 := bstep (se 1 (by rfl) ⟨1464191, by rfl⟩ : syracuseStep 1952255 = 2928383) B2928383
theorem B33410663 : Blo 1156638 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B6607291 : Blo 1156638 6607291 := bstep (se 1 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 6607291 = 9910937) B9910937
theorem B2609819 : Blo 1156638 2609819 := bstep (se 1 (by rfl) ⟨1957364, by rfl⟩ : syracuseStep 2609819 = 3914729) B3914729
theorem B57168659 : Blo 1156638 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B3298441 : Blo 1156638 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B1857071 : Blo 1156638 1857071 := bstep (se 1 (by rfl) ⟨1392803, by rfl⟩ : syracuseStep 1857071 = 2785607) B2785607
theorem B7526621 : Blo 1156638 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B6774025 : Blo 1156638 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B1957513 : Blo 1156638 1957513 := bstep (se 2 (by rfl) ⟨734067, by rfl⟩ : syracuseStep 1957513 = 1468135) B1468135
theorem B7036571 : Blo 1156638 7036571 := bstep (se 1 (by rfl) ⟨5277428, by rfl⟩ : syracuseStep 7036571 = 10554857) B10554857
theorem B3301505 : Blo 1156638 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B12545351 : Blo 1156638 12545351 := bstep (se 1 (by rfl) ⟨9409013, by rfl⟩ : syracuseStep 12545351 = 18818027) B18818027
theorem B8810207 : Blo 1156638 8810207 := bstep (se 1 (by rfl) ⟨6607655, by rfl⟩ : syracuseStep 8810207 = 13215311) B13215311
theorem B15855659 : Blo 1156638 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B16675807 : Blo 1156638 16675807 := bstep (se 1 (by rfl) ⟨12506855, by rfl⟩ : syracuseStep 16675807 = 25013711) B25013711
theorem B6256871 : Blo 1156638 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B6256889 : Blo 1156638 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B7043867 : Blo 1156638 7043867 := bstep (se 1 (by rfl) ⟨5282900, by rfl⟩ : syracuseStep 7043867 = 10565801) B10565801
theorem B7142537 : Blo 1156638 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B1933535 : Blo 1156638 1933535 := bstep (se 1 (by rfl) ⟨1450151, by rfl⟩ : syracuseStep 1933535 = 2900303) B2900303
theorem B1737023 : Blo 1156638 1737023 := bstep (se 1 (by rfl) ⟨1302767, by rfl⟩ : syracuseStep 1737023 = 2605535) B2605535
theorem B1737695 : Blo 1156638 1737695 := bstep (se 1 (by rfl) ⟨1303271, by rfl⟩ : syracuseStep 1737695 = 2606543) B2606543
theorem B2786491 : Blo 1156638 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B1739879 : Blo 1156638 1739879 := bstep (se 1 (by rfl) ⟨1304909, by rfl⟩ : syracuseStep 1739879 = 2609819) B2609819
theorem B38112439 : Blo 1156638 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B4395991 : Blo 1156638 4395991 := bstep (se 1 (by rfl) ⟨3296993, by rfl⟩ : syracuseStep 4395991 = 6593987) B6593987
theorem B4691047 : Blo 1156638 4691047 := bstep (se 1 (by rfl) ⟨3518285, by rfl⟩ : syracuseStep 4691047 = 7036571) B7036571
theorem B2201003 : Blo 1156638 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B11146729 : Blo 1156638 11146729 := bstep (se 2 (by rfl) ⟨4180023, by rfl⟩ : syracuseStep 11146729 = 8360047) B8360047
theorem B4397921 : Blo 1156638 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B18553799 : Blo 1156638 18553799 := bstep (se 1 (by rfl) ⟨13915349, by rfl⟩ : syracuseStep 18553799 = 27830699) B27830699
theorem B8363567 : Blo 1156638 8363567 := bstep (se 1 (by rfl) ⟨6272675, by rfl⟩ : syracuseStep 8363567 = 12545351) B12545351
theorem B5873471 : Blo 1156638 5873471 := bstep (se 1 (by rfl) ⟨4405103, by rfl⟩ : syracuseStep 5873471 = 8810207) B8810207
theorem B19046765 : Blo 1156638 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B4171247 : Blo 1156638 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B4171259 : Blo 1156638 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B4400639 : Blo 1156638 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B42280703 : Blo 1156638 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B4695911 : Blo 1156638 4695911 := bstep (se 1 (by rfl) ⟨3521933, by rfl⟩ : syracuseStep 4695911 = 7043867) B7043867
theorem B8792225 : Blo 1156638 8792225 := bstep (se 2 (by rfl) ⟨3297084, by rfl⟩ : syracuseStep 8792225 = 6594169) B6594169
theorem B1158127 : Blo 1156638 1158127 := bstep (se 1 (by rfl) ⟨868595, by rfl⟩ : syracuseStep 1158127 = 1737191) B1737191
theorem B21114017 : Blo 1156638 21114017 := bstep (se 2 (by rfl) ⟨7917756, by rfl⟩ : syracuseStep 21114017 = 15835513) B15835513
theorem B1158911 : Blo 1156638 1158911 := bstep (se 1 (by rfl) ⟨869183, by rfl⟩ : syracuseStep 1158911 = 1738367) B1738367
theorem B1158939 : Blo 1156638 1158939 := bstep (se 1 (by rfl) ⟨869204, by rfl⟩ : syracuseStep 1158939 = 1738409) B1738409
theorem B1159079 : Blo 1156638 1159079 := bstep (se 1 (by rfl) ⟨869309, by rfl⟩ : syracuseStep 1159079 = 1738619) B1738619
theorem B1159835 : Blo 1156638 1159835 := bstep (se 1 (by rfl) ⟨869876, by rfl⟩ : syracuseStep 1159835 = 1739753) B1739753
theorem B1160063 : Blo 1156638 1160063 := bstep (se 1 (by rfl) ⟨870047, by rfl⟩ : syracuseStep 1160063 = 1740095) B1740095
theorem B1160223 : Blo 1156638 1160223 := bstep (se 1 (by rfl) ⟨870167, by rfl⟩ : syracuseStep 1160223 = 1740335) B1740335
theorem B2602727 : Blo 1156638 2602727 := bstep (se 1 (by rfl) ⟨1952045, by rfl⟩ : syracuseStep 2602727 = 3904091) B3904091
theorem B2604671 : Blo 1156638 2604671 := bstep (se 1 (by rfl) ⟨1953503, by rfl⟩ : syracuseStep 2604671 = 3907007) B3907007
theorem B20070989 : Blo 1156638 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B2606111 : Blo 1156638 2606111 := bstep (se 1 (by rfl) ⟨1954583, by rfl⟩ : syracuseStep 2606111 = 3909167) B3909167
theorem B22234409 : Blo 1156638 22234409 := bstep (se 2 (by rfl) ⟨8337903, by rfl⟩ : syracuseStep 22234409 = 16675807) B16675807
theorem B15845635 : Blo 1156638 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B10570439 : Blo 1156638 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B9032033 : Blo 1156638 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B2610017 : Blo 1156638 2610017 := bstep (se 2 (by rfl) ⟨978756, by rfl⟩ : syracuseStep 2610017 = 1957513) B1957513
theorem B40162463 : Blo 1156638 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B28530089 : Blo 1156638 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B5560987 : Blo 1156638 5560987 := bstep (se 1 (by rfl) ⟨4170740, by rfl⟩ : syracuseStep 5560987 = 8341481) B8341481
theorem B3300047 : Blo 1156638 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B5561257 : Blo 1156638 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B1301503 : Blo 1156638 1301503 := bstep (se 1 (by rfl) ⟨976127, by rfl⟩ : syracuseStep 1301503 = 1952255) B1952255
theorem B22273775 : Blo 1156638 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B3301847 : Blo 1156638 3301847 := bstep (se 1 (by rfl) ⟨2476385, by rfl⟩ : syracuseStep 3301847 = 4952771) B4952771
theorem B1238047 : Blo 1156638 1238047 := bstep (se 1 (by rfl) ⟨928535, by rfl⟩ : syracuseStep 1238047 = 1857071) B1857071
theorem B8809721 : Blo 1156638 8809721 := bstep (se 2 (by rfl) ⟨3303645, by rfl⟩ : syracuseStep 8809721 = 6607291) B6607291
theorem B7436279 : Blo 1156638 7436279 := bstep (se 1 (by rfl) ⟨5577209, by rfl⟩ : syracuseStep 7436279 = 11154419) B11154419
theorem B5863913 : Blo 1156638 5863913 := bstep (se 2 (by rfl) ⟨2198967, by rfl⟩ : syracuseStep 5863913 = 4397935) B4397935
theorem B1735487 : Blo 1156638 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B1735871 : Blo 1156638 1735871 := bstep (se 1 (by rfl) ⟨1301903, by rfl⟩ : syracuseStep 1735871 = 2603807) B2603807
theorem B1736027 : Blo 1156638 1736027 := bstep (se 1 (by rfl) ⟨1302020, by rfl⟩ : syracuseStep 1736027 = 2604041) B2604041
theorem B1737407 : Blo 1156638 1737407 := bstep (se 1 (by rfl) ⟨1303055, by rfl⟩ : syracuseStep 1737407 = 2606111) B2606111
theorem B24085421 : Blo 1156638 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B7046959 : Blo 1156638 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B1740011 : Blo 1156638 1740011 := bstep (se 1 (by rfl) ⟨1305008, by rfl⟩ : syracuseStep 1740011 = 2610017) B2610017
theorem B26774975 : Blo 1156638 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2200031 : Blo 1156638 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B5575711 : Blo 1156638 5575711 := bstep (se 1 (by rfl) ⟨4181783, by rfl⟩ : syracuseStep 5575711 = 8363567) B8363567
theorem B14849183 : Blo 1156638 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B2201231 : Blo 1156638 2201231 := bstep (se 1 (by rfl) ⟨1650923, by rfl⟩ : syracuseStep 2201231 = 3301847) B3301847
theorem B28187135 : Blo 1156638 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B5873147 : Blo 1156638 5873147 := bstep (se 1 (by rfl) ⟨4404860, by rfl⟩ : syracuseStep 5873147 = 8809721) B8809721
theorem B7414649 : Blo 1156638 7414649 := bstep (se 2 (by rfl) ⟨2780493, by rfl⟩ : syracuseStep 7414649 = 5560987) B5560987
theorem B7415009 : Blo 1156638 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B4957519 : Blo 1156638 4957519 := bstep (se 1 (by rfl) ⟨3718139, by rfl⟩ : syracuseStep 4957519 = 7436279) B7436279
theorem B3909275 : Blo 1156638 3909275 := bstep (se 1 (by rfl) ⟨2931956, by rfl⟩ : syracuseStep 3909275 = 5863913) B5863913
theorem B1156991 : Blo 1156638 1156991 := bstep (se 1 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 1156991 = 1735487) B1735487
theorem B1157247 : Blo 1156638 1157247 := bstep (se 1 (by rfl) ⟨867935, by rfl⟩ : syracuseStep 1157247 = 1735871) B1735871
theorem B1157351 : Blo 1156638 1157351 := bstep (se 1 (by rfl) ⟨868013, by rfl⟩ : syracuseStep 1157351 = 1736027) B1736027
theorem B1289023 : Blo 1156638 1289023 := bstep (se 1 (by rfl) ⟨966767, by rfl⟩ : syracuseStep 1289023 = 1933535) B1933535
theorem B1158015 : Blo 1156638 1158015 := bstep (se 1 (by rfl) ⟨868511, by rfl⟩ : syracuseStep 1158015 = 1737023) B1737023
theorem B13380659 : Blo 1156638 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B1158463 : Blo 1156638 1158463 := bstep (se 1 (by rfl) ⟨868847, by rfl⟩ : syracuseStep 1158463 = 1737695) B1737695
theorem B14822939 : Blo 1156638 14822939 := bstep (se 1 (by rfl) ⟨11117204, by rfl⟩ : syracuseStep 14822939 = 22234409) B22234409
theorem B3715321 : Blo 1156638 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B1159919 : Blo 1156638 1159919 := bstep (se 1 (by rfl) ⟨869939, by rfl⟩ : syracuseStep 1159919 = 1739879) B1739879
theorem B19020059 : Blo 1156638 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B2931947 : Blo 1156638 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B12369199 : Blo 1156638 12369199 := bstep (se 1 (by rfl) ⟨9276899, by rfl⟩ : syracuseStep 12369199 = 18553799) B18553799
theorem B3915647 : Blo 1156638 3915647 := bstep (se 1 (by rfl) ⟨2936735, by rfl⟩ : syracuseStep 3915647 = 5873471) B5873471
theorem B6602917 : Blo 1156638 6602917 := bstep (se 4 (by rfl) ⟨619023, by rfl⟩ : syracuseStep 6602917 = 1238047) B1238047
theorem B12697843 : Blo 1156638 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B2933759 : Blo 1156638 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B3130607 : Blo 1156638 3130607 := bstep (se 1 (by rfl) ⟨2347955, by rfl⟩ : syracuseStep 3130607 = 4695911) B4695911
theorem B14862305 : Blo 1156638 14862305 := bstep (se 2 (by rfl) ⟨5573364, by rfl⟩ : syracuseStep 14862305 = 11146729) B11146729
theorem B14076011 : Blo 1156638 14076011 := bstep (se 1 (by rfl) ⟨10557008, by rfl⟩ : syracuseStep 14076011 = 21114017) B21114017
theorem B21127513 : Blo 1156638 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B1467335 : Blo 1156638 1467335 := bstep (se 1 (by rfl) ⟨1100501, by rfl⟩ : syracuseStep 1467335 = 2201003) B2201003
theorem B50816585 : Blo 1156638 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B2780831 : Blo 1156638 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B2780839 : Blo 1156638 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B5861321 : Blo 1156638 5861321 := bstep (se 2 (by rfl) ⟨2197995, by rfl⟩ : syracuseStep 5861321 = 4395991) B4395991
theorem B5861483 : Blo 1156638 5861483 := bstep (se 1 (by rfl) ⟨4396112, by rfl⟩ : syracuseStep 5861483 = 8792225) B8792225
theorem B6254729 : Blo 1156638 6254729 := bstep (se 2 (by rfl) ⟨2345523, by rfl⟩ : syracuseStep 6254729 = 4691047) B4691047
theorem B1735151 : Blo 1156638 1735151 := bstep (se 1 (by rfl) ⟨1301363, by rfl⟩ : syracuseStep 1735151 = 2602727) B2602727
theorem B1735337 : Blo 1156638 1735337 := bstep (se 2 (by rfl) ⟨650751, by rfl⟩ : syracuseStep 1735337 = 1301503) B1301503
theorem B1736447 : Blo 1156638 1736447 := bstep (se 1 (by rfl) ⟨1302335, by rfl⟩ : syracuseStep 1736447 = 2604671) B2604671
theorem B16056947 : Blo 1156638 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B9899455 : Blo 1156638 9899455 := bstep (se 1 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 9899455 = 14849183) B14849183
theorem B3707785 : Blo 1156638 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B4953761 : Blo 1156638 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B8920439 : Blo 1156638 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B3907547 : Blo 1156638 3907547 := bstep (se 1 (by rfl) ⟨2930660, by rfl⟩ : syracuseStep 3907547 = 5861321) B5861321
theorem B3907655 : Blo 1156638 3907655 := bstep (se 1 (by rfl) ⟨2930741, by rfl⟩ : syracuseStep 3907655 = 5861483) B5861483
theorem B4169819 : Blo 1156638 4169819 := bstep (se 1 (by rfl) ⟨3127364, by rfl⟩ : syracuseStep 4169819 = 6254729) B6254729
theorem B1156767 : Blo 1156638 1156767 := bstep (se 1 (by rfl) ⟨867575, by rfl⟩ : syracuseStep 1156767 = 1735151) B1735151
theorem B16492265 : Blo 1156638 16492265 := bstep (se 2 (by rfl) ⟨6184599, by rfl⟩ : syracuseStep 16492265 = 12369199) B12369199
theorem B7415549 : Blo 1156638 7415549 := bstep (se 3 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 7415549 = 2780831) B2780831
theorem B1156891 : Blo 1156638 1156891 := bstep (se 1 (by rfl) ⟨867668, by rfl⟩ : syracuseStep 1156891 = 1735337) B1735337
theorem B1157631 : Blo 1156638 1157631 := bstep (se 1 (by rfl) ⟨868223, by rfl⟩ : syracuseStep 1157631 = 1736447) B1736447
theorem B1158271 : Blo 1156638 1158271 := bstep (se 1 (by rfl) ⟨868703, by rfl⟩ : syracuseStep 1158271 = 1737407) B1737407
theorem B9908203 : Blo 1156638 9908203 := bstep (se 1 (by rfl) ⟨7431152, by rfl⟩ : syracuseStep 9908203 = 14862305) B14862305
theorem B9384007 : Blo 1156638 9384007 := bstep (se 1 (by rfl) ⟨7038005, by rfl⟩ : syracuseStep 9384007 = 14076011) B14076011
theorem B1160007 : Blo 1156638 1160007 := bstep (se 1 (by rfl) ⟨870005, by rfl⟩ : syracuseStep 1160007 = 1740011) B1740011
theorem B3912893 : Blo 1156638 3912893 := bstep (se 3 (by rfl) ⟨733667, by rfl⟩ : syracuseStep 3912893 = 1467335) B1467335
theorem B135510893 : Blo 1156638 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B18791423 : Blo 1156638 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B3915431 : Blo 1156638 3915431 := bstep (se 1 (by rfl) ⟨2936573, by rfl⟩ : syracuseStep 3915431 = 5873147) B5873147
theorem B2606183 : Blo 1156638 2606183 := bstep (se 1 (by rfl) ⟨1954637, by rfl⟩ : syracuseStep 2606183 = 3909275) B3909275
theorem B9881959 : Blo 1156638 9881959 := bstep (se 1 (by rfl) ⟨7411469, by rfl⟩ : syracuseStep 9881959 = 14822939) B14822939
theorem B1954631 : Blo 1156638 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B2610431 : Blo 1156638 2610431 := bstep (se 1 (by rfl) ⟨1957823, by rfl⟩ : syracuseStep 2610431 = 3915647) B3915647
theorem B8803889 : Blo 1156638 8803889 := bstep (se 2 (by rfl) ⟨3301458, by rfl⟩ : syracuseStep 8803889 = 6602917) B6602917
theorem B16930457 : Blo 1156638 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B28170017 : Blo 1156638 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B1955839 : Blo 1156638 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B6610025 : Blo 1156638 6610025 := bstep (se 2 (by rfl) ⟨2478759, by rfl⟩ : syracuseStep 6610025 = 4957519) B4957519
theorem B17849983 : Blo 1156638 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B9395945 : Blo 1156638 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B1466687 : Blo 1156638 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B8348285 : Blo 1156638 8348285 := bstep (se 3 (by rfl) ⟨1565303, by rfl⟩ : syracuseStep 8348285 = 3130607) B3130607
theorem B1467487 : Blo 1156638 1467487 := bstep (se 1 (by rfl) ⟨1100615, by rfl⟩ : syracuseStep 1467487 = 2201231) B2201231
theorem B6874789 : Blo 1156638 6874789 := bstep (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) B1289023
theorem B4943099 : Blo 1156638 4943099 := bstep (se 1 (by rfl) ⟨3707324, by rfl⟩ : syracuseStep 4943099 = 7414649) B7414649
theorem B4943339 : Blo 1156638 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B7434281 : Blo 1156638 7434281 := bstep (se 2 (by rfl) ⟨2787855, by rfl⟩ : syracuseStep 7434281 = 5575711) B5575711
theorem B12680039 : Blo 1156638 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B1737455 : Blo 1156638 1737455 := bstep (se 1 (by rfl) ⟨1303091, by rfl⟩ : syracuseStep 1737455 = 2606183) B2606183
theorem B13175945 : Blo 1156638 13175945 := bstep (se 2 (by rfl) ⟨4940979, by rfl⟩ : syracuseStep 13175945 = 9881959) B9881959
theorem B1740287 : Blo 1156638 1740287 := bstep (se 1 (by rfl) ⟨1305215, by rfl⟩ : syracuseStep 1740287 = 2610431) B2610431
theorem B5869259 : Blo 1156638 5869259 := bstep (se 1 (by rfl) ⟨4401944, by rfl⟩ : syracuseStep 5869259 = 8803889) B8803889
theorem B18780011 : Blo 1156638 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B6263963 : Blo 1156638 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B13210937 : Blo 1156638 13210937 := bstep (se 2 (by rfl) ⟨4954101, by rfl⟩ : syracuseStep 13210937 = 9908203) B9908203
theorem B4956187 : Blo 1156638 4956187 := bstep (se 1 (by rfl) ⟨3717140, by rfl⟩ : syracuseStep 4956187 = 7434281) B7434281
theorem B12527615 : Blo 1156638 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B23799977 : Blo 1156638 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B3911165 : Blo 1156638 3911165 := bstep (se 3 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 3911165 = 1466687) B1466687
theorem B11286971 : Blo 1156638 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B19774853 : Blo 1156638 19774853 := bstep (se 4 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 19774853 = 3707785) B3707785
theorem B4406683 : Blo 1156638 4406683 := bstep (se 1 (by rfl) ⟨3305012, by rfl⟩ : syracuseStep 4406683 = 6610025) B6610025
theorem B5946959 : Blo 1156638 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B2605031 : Blo 1156638 2605031 := bstep (se 1 (by rfl) ⟨1953773, by rfl⟩ : syracuseStep 2605031 = 3907547) B3907547
theorem B2605103 : Blo 1156638 2605103 := bstep (se 1 (by rfl) ⟨1953827, by rfl⟩ : syracuseStep 2605103 = 3907655) B3907655
theorem B3295399 : Blo 1156638 3295399 := bstep (se 1 (by rfl) ⟨2471549, by rfl⟩ : syracuseStep 3295399 = 4943099) B4943099
theorem B3295559 : Blo 1156638 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B175917493 : Blo 1156638 175917493 := bstep (se 5 (by rfl) ⟨8246132, by rfl⟩ : syracuseStep 175917493 = 16492265) B16492265
theorem B2607785 : Blo 1156638 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B2608595 : Blo 1156638 2608595 := bstep (se 1 (by rfl) ⟨1956446, by rfl⟩ : syracuseStep 2608595 = 3912893) B3912893
theorem B2610287 : Blo 1156638 2610287 := bstep (se 1 (by rfl) ⟨1957715, by rfl⟩ : syracuseStep 2610287 = 3915431) B3915431
theorem B10704631 : Blo 1156638 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B1956649 : Blo 1156638 1956649 := bstep (se 2 (by rfl) ⟨733743, by rfl⟩ : syracuseStep 1956649 = 1467487) B1467487
theorem B9166385 : Blo 1156638 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B1303087 : Blo 1156638 1303087 := bstep (se 1 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 1303087 = 1954631) B1954631
theorem B3302507 : Blo 1156638 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B13199273 : Blo 1156638 13199273 := bstep (se 2 (by rfl) ⟨4949727, by rfl⟩ : syracuseStep 13199273 = 9899455) B9899455
theorem B2779879 : Blo 1156638 2779879 := bstep (se 1 (by rfl) ⟨2084909, by rfl⟩ : syracuseStep 2779879 = 4169819) B4169819
theorem B12512009 : Blo 1156638 12512009 := bstep (se 2 (by rfl) ⟨4692003, by rfl⟩ : syracuseStep 12512009 = 9384007) B9384007
theorem B5565523 : Blo 1156638 5565523 := bstep (se 1 (by rfl) ⟨4174142, by rfl⟩ : syracuseStep 5565523 = 8348285) B8348285
theorem B4943699 : Blo 1156638 4943699 := bstep (se 1 (by rfl) ⟨3707774, by rfl⟩ : syracuseStep 4943699 = 7415549) B7415549
theorem B8453359 : Blo 1156638 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B90340595 : Blo 1156638 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B1736735 : Blo 1156638 1736735 := bstep (se 1 (by rfl) ⟨1302551, by rfl⟩ : syracuseStep 1736735 = 2605103) B2605103
theorem B1737449 : Blo 1156638 1737449 := bstep (se 2 (by rfl) ⟨651543, by rfl⟩ : syracuseStep 1737449 = 1303087) B1303087
theorem B2197039 : Blo 1156638 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B1738523 : Blo 1156638 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B8783963 : Blo 1156638 8783963 := bstep (se 1 (by rfl) ⟨6587972, by rfl⟩ : syracuseStep 8783963 = 13175945) B13175945
theorem B1739063 : Blo 1156638 1739063 := bstep (se 1 (by rfl) ⟨1304297, by rfl⟩ : syracuseStep 1739063 = 2608595) B2608595
theorem B12520007 : Blo 1156638 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B4393865 : Blo 1156638 4393865 := bstep (se 2 (by rfl) ⟨1647699, by rfl⟩ : syracuseStep 4393865 = 3295399) B3295399
theorem B234556657 : Blo 1156638 234556657 := bstep (se 2 (by rfl) ⟨87958746, by rfl⟩ : syracuseStep 234556657 = 175917493) B175917493
theorem B1740191 : Blo 1156638 1740191 := bstep (se 1 (by rfl) ⟨1305143, by rfl⟩ : syracuseStep 1740191 = 2610287) B2610287
theorem B3706505 : Blo 1156638 3706505 := bstep (se 2 (by rfl) ⟨1389939, by rfl⟩ : syracuseStep 3706505 = 2779879) B2779879
theorem B2201671 : Blo 1156638 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B15866651 : Blo 1156638 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B5875577 : Blo 1156638 5875577 := bstep (se 2 (by rfl) ⟨2203341, by rfl⟩ : syracuseStep 5875577 = 4406683) B4406683
theorem B13183235 : Blo 1156638 13183235 := bstep (se 1 (by rfl) ⟨9887426, by rfl⟩ : syracuseStep 13183235 = 19774853) B19774853
theorem B1158303 : Blo 1156638 1158303 := bstep (se 1 (by rfl) ⟨868727, by rfl⟩ : syracuseStep 1158303 = 1737455) B1737455
theorem B1160191 : Blo 1156638 1160191 := bstep (se 1 (by rfl) ⟨870143, by rfl⟩ : syracuseStep 1160191 = 1740287) B1740287
theorem B3912839 : Blo 1156638 3912839 := bstep (se 1 (by rfl) ⟨2934629, by rfl⟩ : syracuseStep 3912839 = 5869259) B5869259
theorem B4175975 : Blo 1156638 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B7420697 : Blo 1156638 7420697 := bstep (se 2 (by rfl) ⟨2782761, by rfl⟩ : syracuseStep 7420697 = 5565523) B5565523
theorem B6110923 : Blo 1156638 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B8799515 : Blo 1156638 8799515 := bstep (se 1 (by rfl) ⟨6599636, by rfl⟩ : syracuseStep 8799515 = 13199273) B13199273
theorem B8341339 : Blo 1156638 8341339 := bstep (se 1 (by rfl) ⟨6256004, by rfl⟩ : syracuseStep 8341339 = 12512009) B12512009
theorem B14272841 : Blo 1156638 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B2607443 : Blo 1156638 2607443 := bstep (se 1 (by rfl) ⟨1955582, by rfl⟩ : syracuseStep 2607443 = 3911165) B3911165
theorem B3295799 : Blo 1156638 3295799 := bstep (se 1 (by rfl) ⟨2471849, by rfl⟩ : syracuseStep 3295799 = 4943699) B4943699
theorem B2608865 : Blo 1156638 2608865 := bstep (se 2 (by rfl) ⟨978324, by rfl⟩ : syracuseStep 2608865 = 1956649) B1956649
theorem B7524647 : Blo 1156638 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B6608249 : Blo 1156638 6608249 := bstep (se 2 (by rfl) ⟨2478093, by rfl⟩ : syracuseStep 6608249 = 4956187) B4956187
theorem B8807291 : Blo 1156638 8807291 := bstep (se 1 (by rfl) ⟨6605468, by rfl⟩ : syracuseStep 8807291 = 13210937) B13210937
theorem B8351743 : Blo 1156638 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B11271145 : Blo 1156638 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B60227063 : Blo 1156638 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B3964639 : Blo 1156638 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B1736687 : Blo 1156638 1736687 := bstep (se 1 (by rfl) ⟨1302515, by rfl⟩ : syracuseStep 1736687 = 2605031) B2605031
theorem B5866343 : Blo 1156638 5866343 := bstep (se 1 (by rfl) ⟨4399757, by rfl⟩ : syracuseStep 5866343 = 8799515) B8799515
theorem B1738295 : Blo 1156638 1738295 := bstep (se 1 (by rfl) ⟨1303721, by rfl⟩ : syracuseStep 1738295 = 2607443) B2607443
theorem B2197199 : Blo 1156638 2197199 := bstep (se 1 (by rfl) ⟨1647899, by rfl⟩ : syracuseStep 2197199 = 3295799) B3295799
theorem B1739243 : Blo 1156638 1739243 := bstep (se 1 (by rfl) ⟨1304432, by rfl⟩ : syracuseStep 1739243 = 2608865) B2608865
theorem B5016431 : Blo 1156638 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B5003875349 : Blo 1156638 5003875349 := bstep (se 6 (by rfl) ⟨117278328, by rfl⟩ : syracuseStep 5003875349 = 234556657) B234556657
theorem B5871527 : Blo 1156638 5871527 := bstep (se 1 (by rfl) ⟨4403645, by rfl⟩ : syracuseStep 5871527 = 8807291) B8807291
theorem B8788823 : Blo 1156638 8788823 := bstep (se 1 (by rfl) ⟨6591617, by rfl⟩ : syracuseStep 8788823 = 13183235) B13183235
theorem B42311069 : Blo 1156638 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B5286185 : Blo 1156638 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B40151375 : Blo 1156638 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B1157791 : Blo 1156638 1157791 := bstep (se 1 (by rfl) ⟨868343, by rfl⟩ : syracuseStep 1157791 = 1736687) B1736687
theorem B1157823 : Blo 1156638 1157823 := bstep (se 1 (by rfl) ⟨868367, by rfl⟩ : syracuseStep 1157823 = 1736735) B1736735
theorem B1158299 : Blo 1156638 1158299 := bstep (se 1 (by rfl) ⟨868724, by rfl⟩ : syracuseStep 1158299 = 1737449) B1737449
theorem B1159015 : Blo 1156638 1159015 := bstep (se 1 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 1159015 = 1738523) B1738523
theorem B1159375 : Blo 1156638 1159375 := bstep (se 1 (by rfl) ⟨869531, by rfl⟩ : syracuseStep 1159375 = 1739063) B1739063
theorem B9515227 : Blo 1156638 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B2929243 : Blo 1156638 2929243 := bstep (se 1 (by rfl) ⟨2196932, by rfl⟩ : syracuseStep 2929243 = 4393865) B4393865
theorem B2929385 : Blo 1156638 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B1160127 : Blo 1156638 1160127 := bstep (se 1 (by rfl) ⟨870095, by rfl⟩ : syracuseStep 1160127 = 1740191) B1740191
theorem B2471003 : Blo 1156638 2471003 := bstep (se 1 (by rfl) ⟨1853252, by rfl⟩ : syracuseStep 2471003 = 3706505) B3706505
theorem B11121785 : Blo 1156638 11121785 := bstep (se 2 (by rfl) ⟨4170669, by rfl⟩ : syracuseStep 11121785 = 8341339) B8341339
theorem B4405499 : Blo 1156638 4405499 := bstep (se 1 (by rfl) ⟨3304124, by rfl⟩ : syracuseStep 4405499 = 6608249) B6608249
theorem B3917051 : Blo 1156638 3917051 := bstep (se 1 (by rfl) ⟨2937788, by rfl⟩ : syracuseStep 3917051 = 5875577) B5875577
theorem B2935561 : Blo 1156638 2935561 := bstep (se 2 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 2935561 = 2201671) B2201671
theorem B2608559 : Blo 1156638 2608559 := bstep (se 1 (by rfl) ⟨1956419, by rfl⟩ : syracuseStep 2608559 = 3912839) B3912839
theorem B15028193 : Blo 1156638 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B8147897 : Blo 1156638 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B5855975 : Blo 1156638 5855975 := bstep (se 1 (by rfl) ⟨4391981, by rfl⟩ : syracuseStep 5855975 = 8783963) B8783963
theorem B8346671 : Blo 1156638 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B11135657 : Blo 1156638 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B2783983 : Blo 1156638 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B4947131 : Blo 1156638 4947131 := bstep (se 1 (by rfl) ⟨3710348, by rfl⟩ : syracuseStep 4947131 = 7420697) B7420697
theorem B1739039 : Blo 1156638 1739039 := bstep (se 1 (by rfl) ⟨1304279, by rfl⟩ : syracuseStep 1739039 = 2608559) B2608559
theorem B3335916899 : Blo 1156638 3335916899 := bstep (se 1 (by rfl) ⟨2501937674, by rfl⟩ : syracuseStep 3335916899 = 5003875349) B5003875349
theorem B3903983 : Blo 1156638 3903983 := bstep (se 1 (by rfl) ⟨2927987, by rfl⟩ : syracuseStep 3903983 = 5855975) B5855975
theorem B12686969 : Blo 1156638 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B3905657 : Blo 1156638 3905657 := bstep (se 2 (by rfl) ⟨1464621, by rfl⟩ : syracuseStep 3905657 = 2929243) B2929243
theorem B29695085 : Blo 1156638 29695085 := bstep (se 3 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 29695085 = 11135657) B11135657
theorem B13377149 : Blo 1156638 13377149 := bstep (se 3 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 13377149 = 5016431) B5016431
theorem B1647335 : Blo 1156638 1647335 := bstep (se 1 (by rfl) ⟨1235501, by rfl⟩ : syracuseStep 1647335 = 2471003) B2471003
theorem B7414523 : Blo 1156638 7414523 := bstep (se 1 (by rfl) ⟨5560892, by rfl⟩ : syracuseStep 7414523 = 11121785) B11121785
theorem B3711977 : Blo 1156638 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B3910895 : Blo 1156638 3910895 := bstep (se 1 (by rfl) ⟨2933171, by rfl⟩ : syracuseStep 3910895 = 5866343) B5866343
theorem B1158863 : Blo 1156638 1158863 := bstep (se 1 (by rfl) ⟨869147, by rfl⟩ : syracuseStep 1158863 = 1738295) B1738295
theorem B1159495 : Blo 1156638 1159495 := bstep (se 1 (by rfl) ⟨869621, by rfl⟩ : syracuseStep 1159495 = 1739243) B1739243
theorem B3914081 : Blo 1156638 3914081 := bstep (se 2 (by rfl) ⟨1467780, by rfl⟩ : syracuseStep 3914081 = 2935561) B2935561
theorem B3914351 : Blo 1156638 3914351 := bstep (se 1 (by rfl) ⟨2935763, by rfl⟩ : syracuseStep 3914351 = 5871527) B5871527
theorem B3524123 : Blo 1156638 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B1952923 : Blo 1156638 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B2936999 : Blo 1156638 2936999 := bstep (se 1 (by rfl) ⟨2202749, by rfl⟩ : syracuseStep 2936999 = 4405499) B4405499
theorem B3298087 : Blo 1156638 3298087 := bstep (se 1 (by rfl) ⟨2473565, by rfl⟩ : syracuseStep 3298087 = 4947131) B4947131
theorem B2611367 : Blo 1156638 2611367 := bstep (se 1 (by rfl) ⟨1958525, by rfl⟩ : syracuseStep 2611367 = 3917051) B3917051
theorem B1464799 : Blo 1156638 1464799 := bstep (se 1 (by rfl) ⟨1098599, by rfl⟩ : syracuseStep 1464799 = 2197199) B2197199
theorem B5431931 : Blo 1156638 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B5859215 : Blo 1156638 5859215 := bstep (se 1 (by rfl) ⟨4394411, by rfl⟩ : syracuseStep 5859215 = 8788823) B8788823
theorem B5564447 : Blo 1156638 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B28207379 : Blo 1156638 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B26767583 : Blo 1156638 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B40075181 : Blo 1156638 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B4392893 : Blo 1156638 4392893 := bstep (se 3 (by rfl) ⟨823667, by rfl⟩ : syracuseStep 4392893 = 1647335) B1647335
theorem B8457979 : Blo 1156638 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B1740911 : Blo 1156638 1740911 := bstep (se 1 (by rfl) ⟨1305683, by rfl⟩ : syracuseStep 1740911 = 2611367) B2611367
theorem B19796723 : Blo 1156638 19796723 := bstep (se 1 (by rfl) ⟨14847542, by rfl⟩ : syracuseStep 19796723 = 29695085) B29695085
theorem B8918099 : Blo 1156638 8918099 := bstep (se 1 (by rfl) ⟨6688574, by rfl⟩ : syracuseStep 8918099 = 13377149) B13377149
theorem B4397449 : Blo 1156638 4397449 := bstep (se 2 (by rfl) ⟨1649043, by rfl⟩ : syracuseStep 4397449 = 3298087) B3298087
theorem B3906143 : Blo 1156638 3906143 := bstep (se 1 (by rfl) ⟨2929607, by rfl⟩ : syracuseStep 3906143 = 5859215) B5859215
theorem B3709631 : Blo 1156638 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B26716787 : Blo 1156638 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B1159359 : Blo 1156638 1159359 := bstep (se 1 (by rfl) ⟨869519, by rfl⟩ : syracuseStep 1159359 = 1739039) B1739039
theorem B2223944599 : Blo 1156638 2223944599 := bstep (se 1 (by rfl) ⟨1667958449, by rfl⟩ : syracuseStep 2223944599 = 3335916899) B3335916899
theorem B2602655 : Blo 1156638 2602655 := bstep (se 1 (by rfl) ⟨1951991, by rfl⟩ : syracuseStep 2602655 = 3903983) B3903983
theorem B2603771 : Blo 1156638 2603771 := bstep (se 1 (by rfl) ⟨1952828, by rfl⟩ : syracuseStep 2603771 = 3905657) B3905657
theorem B2603897 : Blo 1156638 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B3621287 : Blo 1156638 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B2474651 : Blo 1156638 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B2607263 : Blo 1156638 2607263 := bstep (se 1 (by rfl) ⟨1955447, by rfl⟩ : syracuseStep 2607263 = 3910895) B3910895
theorem B17845055 : Blo 1156638 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B1953065 : Blo 1156638 1953065 := bstep (se 2 (by rfl) ⟨732399, by rfl⟩ : syracuseStep 1953065 = 1464799) B1464799
theorem B2609387 : Blo 1156638 2609387 := bstep (se 1 (by rfl) ⟨1957040, by rfl⟩ : syracuseStep 2609387 = 3914081) B3914081
theorem B2609567 : Blo 1156638 2609567 := bstep (se 1 (by rfl) ⟨1957175, by rfl⟩ : syracuseStep 2609567 = 3914351) B3914351
theorem B2349415 : Blo 1156638 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B1957999 : Blo 1156638 1957999 := bstep (se 1 (by rfl) ⟨1468499, by rfl⟩ : syracuseStep 1957999 = 2936999) B2936999
theorem B4943015 : Blo 1156638 4943015 := bstep (se 1 (by rfl) ⟨3707261, by rfl⟩ : syracuseStep 4943015 = 7414523) B7414523
theorem B18804919 : Blo 1156638 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B1738175 : Blo 1156638 1738175 := bstep (se 1 (by rfl) ⟨1303631, by rfl⟩ : syracuseStep 1738175 = 2607263) B2607263
theorem B11896703 : Blo 1156638 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B1739591 : Blo 1156638 1739591 := bstep (se 1 (by rfl) ⟨1304693, by rfl⟩ : syracuseStep 1739591 = 2609387) B2609387
theorem B1739711 : Blo 1156638 1739711 := bstep (se 1 (by rfl) ⟨1304783, by rfl⟩ : syracuseStep 1739711 = 2609567) B2609567
theorem B11277305 : Blo 1156638 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B25073225 : Blo 1156638 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B2928595 : Blo 1156638 2928595 := bstep (se 1 (by rfl) ⟨2196446, by rfl⟩ : syracuseStep 2928595 = 4392893) B4392893
theorem B6599069 : Blo 1156638 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B12530213 : Blo 1156638 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B1160607 : Blo 1156638 1160607 := bstep (se 1 (by rfl) ⟨870455, by rfl⟩ : syracuseStep 1160607 = 1740911) B1740911
theorem B5945399 : Blo 1156638 5945399 := bstep (se 1 (by rfl) ⟨4459049, by rfl⟩ : syracuseStep 5945399 = 8918099) B8918099
theorem B2604095 : Blo 1156638 2604095 := bstep (se 1 (by rfl) ⟨1953071, by rfl⟩ : syracuseStep 2604095 = 3906143) B3906143
theorem B2473087 : Blo 1156638 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B2965259465 : Blo 1156638 2965259465 := bstep (se 2 (by rfl) ⟨1111972299, by rfl⟩ : syracuseStep 2965259465 = 2223944599) B2223944599
theorem B17811191 : Blo 1156638 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B3295343 : Blo 1156638 3295343 := bstep (se 1 (by rfl) ⟨2471507, by rfl⟩ : syracuseStep 3295343 = 4943015) B4943015
theorem B2610665 : Blo 1156638 2610665 := bstep (se 2 (by rfl) ⟨978999, by rfl⟩ : syracuseStep 2610665 = 1957999) B1957999
theorem B2414191 : Blo 1156638 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B1302043 : Blo 1156638 1302043 := bstep (se 1 (by rfl) ⟨976532, by rfl⟩ : syracuseStep 1302043 = 1953065) B1953065
theorem B13197815 : Blo 1156638 13197815 := bstep (se 1 (by rfl) ⟨9898361, by rfl⟩ : syracuseStep 13197815 = 19796723) B19796723
theorem B5863265 : Blo 1156638 5863265 := bstep (se 2 (by rfl) ⟨2198724, by rfl⟩ : syracuseStep 5863265 = 4397449) B4397449
theorem B1735103 : Blo 1156638 1735103 := bstep (se 1 (by rfl) ⟨1301327, by rfl⟩ : syracuseStep 1735103 = 2602655) B2602655
theorem B1735847 : Blo 1156638 1735847 := bstep (se 1 (by rfl) ⟨1301885, by rfl⟩ : syracuseStep 1735847 = 2603771) B2603771
theorem B1735931 : Blo 1156638 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B7931135 : Blo 1156638 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B2196895 : Blo 1156638 2196895 := bstep (se 1 (by rfl) ⟨1647671, by rfl⟩ : syracuseStep 2196895 = 3295343) B3295343
theorem B1740443 : Blo 1156638 1740443 := bstep (se 1 (by rfl) ⟨1305332, by rfl⟩ : syracuseStep 1740443 = 2610665) B2610665
theorem B16715483 : Blo 1156638 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B3904793 : Blo 1156638 3904793 := bstep (se 2 (by rfl) ⟨1464297, by rfl⟩ : syracuseStep 3904793 = 2928595) B2928595
theorem B3218921 : Blo 1156638 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B4399379 : Blo 1156638 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B3908843 : Blo 1156638 3908843 := bstep (se 1 (by rfl) ⟨2931632, by rfl⟩ : syracuseStep 3908843 = 5863265) B5863265
theorem B1156735 : Blo 1156638 1156735 := bstep (se 1 (by rfl) ⟨867551, by rfl⟩ : syracuseStep 1156735 = 1735103) B1735103
theorem B1157231 : Blo 1156638 1157231 := bstep (se 1 (by rfl) ⟨867923, by rfl⟩ : syracuseStep 1157231 = 1735847) B1735847
theorem B1157287 : Blo 1156638 1157287 := bstep (se 1 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 1157287 = 1735931) B1735931
theorem B1976839643 : Blo 1156638 1976839643 := bstep (se 1 (by rfl) ⟨1482629732, by rfl⟩ : syracuseStep 1976839643 = 2965259465) B2965259465
theorem B1158783 : Blo 1156638 1158783 := bstep (se 1 (by rfl) ⟨869087, by rfl⟩ : syracuseStep 1158783 = 1738175) B1738175
theorem B11874127 : Blo 1156638 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B1159727 : Blo 1156638 1159727 := bstep (se 1 (by rfl) ⟨869795, by rfl⟩ : syracuseStep 1159727 = 1739591) B1739591
theorem B1159807 : Blo 1156638 1159807 := bstep (se 1 (by rfl) ⟨869855, by rfl⟩ : syracuseStep 1159807 = 1739711) B1739711
theorem B7518203 : Blo 1156638 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B8798543 : Blo 1156638 8798543 := bstep (se 1 (by rfl) ⟨6598907, by rfl⟩ : syracuseStep 8798543 = 13197815) B13197815
theorem B3297449 : Blo 1156638 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B8353475 : Blo 1156638 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B3963599 : Blo 1156638 3963599 := bstep (se 1 (by rfl) ⟨2972699, by rfl⟩ : syracuseStep 3963599 = 5945399) B5945399
theorem B1736057 : Blo 1156638 1736057 := bstep (se 2 (by rfl) ⟨651021, by rfl⟩ : syracuseStep 1736057 = 1302043) B1302043
theorem B1736063 : Blo 1156638 1736063 := bstep (se 1 (by rfl) ⟨1302047, by rfl⟩ : syracuseStep 1736063 = 2604095) B2604095
theorem B5865695 : Blo 1156638 5865695 := bstep (se 1 (by rfl) ⟨4399271, by rfl⟩ : syracuseStep 5865695 = 8798543) B8798543
theorem B11143655 : Blo 1156638 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B15832169 : Blo 1156638 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B1157371 : Blo 1156638 1157371 := bstep (se 1 (by rfl) ⟨868028, by rfl⟩ : syracuseStep 1157371 = 1736057) B1736057
theorem B1157375 : Blo 1156638 1157375 := bstep (se 1 (by rfl) ⟨868031, by rfl⟩ : syracuseStep 1157375 = 1736063) B1736063
theorem B8793197 : Blo 1156638 8793197 := bstep (se 3 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 8793197 = 3297449) B3297449
theorem B5287423 : Blo 1156638 5287423 := bstep (se 1 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 5287423 = 7931135) B7931135
theorem B2929193 : Blo 1156638 2929193 := bstep (se 2 (by rfl) ⟨1098447, by rfl⟩ : syracuseStep 2929193 = 2196895) B2196895
theorem B1160295 : Blo 1156638 1160295 := bstep (se 1 (by rfl) ⟨870221, by rfl⟩ : syracuseStep 1160295 = 1740443) B1740443
theorem B2603195 : Blo 1156638 2603195 := bstep (se 1 (by rfl) ⟨1952396, by rfl⟩ : syracuseStep 2603195 = 3904793) B3904793
theorem B2145947 : Blo 1156638 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B2932919 : Blo 1156638 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B2605895 : Blo 1156638 2605895 := bstep (se 1 (by rfl) ⟨1954421, by rfl⟩ : syracuseStep 2605895 = 3908843) B3908843
theorem B2642399 : Blo 1156638 2642399 := bstep (se 1 (by rfl) ⟨1981799, by rfl⟩ : syracuseStep 2642399 = 3963599) B3963599
theorem B1317893095 : Blo 1156638 1317893095 := bstep (se 1 (by rfl) ⟨988419821, by rfl⟩ : syracuseStep 1317893095 = 1976839643) B1976839643
theorem B5568983 : Blo 1156638 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B5012135 : Blo 1156638 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B1737263 : Blo 1156638 1737263 := bstep (se 1 (by rfl) ⟨1302947, by rfl⟩ : syracuseStep 1737263 = 2605895) B2605895
theorem B10554779 : Blo 1156638 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B7049897 : Blo 1156638 7049897 := bstep (se 2 (by rfl) ⟨2643711, by rfl⟩ : syracuseStep 7049897 = 5287423) B5287423
theorem B1757190793 : Blo 1156638 1757190793 := bstep (se 2 (by rfl) ⟨658946547, by rfl⟩ : syracuseStep 1757190793 = 1317893095) B1317893095
theorem B3712655 : Blo 1156638 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B3910463 : Blo 1156638 3910463 := bstep (se 1 (by rfl) ⟨2932847, by rfl⟩ : syracuseStep 3910463 = 5865695) B5865695
theorem B1952795 : Blo 1156638 1952795 := bstep (se 1 (by rfl) ⟨1464596, by rfl⟩ : syracuseStep 1952795 = 2929193) B2929193
theorem B5722525 : Blo 1156638 5722525 := bstep (se 3 (by rfl) ⟨1072973, by rfl⟩ : syracuseStep 5722525 = 2145947) B2145947
theorem B1955279 : Blo 1156638 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B7429103 : Blo 1156638 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B1761599 : Blo 1156638 1761599 := bstep (se 1 (by rfl) ⟨1321199, by rfl⟩ : syracuseStep 1761599 = 2642399) B2642399
theorem B5862131 : Blo 1156638 5862131 := bstep (se 1 (by rfl) ⟨4396598, by rfl⟩ : syracuseStep 5862131 = 8793197) B8793197
theorem B1735463 : Blo 1156638 1735463 := bstep (se 1 (by rfl) ⟨1301597, by rfl⟩ : syracuseStep 1735463 = 2603195) B2603195
theorem B3341423 : Blo 1156638 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B9900413 : Blo 1156638 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B4952735 : Blo 1156638 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B3908087 : Blo 1156638 3908087 := bstep (se 1 (by rfl) ⟨2931065, by rfl⟩ : syracuseStep 3908087 = 5862131) B5862131
theorem B2342921057 : Blo 1156638 2342921057 := bstep (se 2 (by rfl) ⟨878595396, by rfl⟩ : syracuseStep 2342921057 = 1757190793) B1757190793
theorem B1156975 : Blo 1156638 1156975 := bstep (se 1 (by rfl) ⟨867731, by rfl⟩ : syracuseStep 1156975 = 1735463) B1735463
theorem B1158175 : Blo 1156638 1158175 := bstep (se 1 (by rfl) ⟨868631, by rfl⟩ : syracuseStep 1158175 = 1737263) B1737263
theorem B4697597 : Blo 1156638 4697597 := bstep (se 3 (by rfl) ⟨880799, by rfl⟩ : syracuseStep 4697597 = 1761599) B1761599
theorem B2606975 : Blo 1156638 2606975 := bstep (se 1 (by rfl) ⟨1955231, by rfl⟩ : syracuseStep 2606975 = 3910463) B3910463
theorem B1301863 : Blo 1156638 1301863 := bstep (se 1 (by rfl) ⟨976397, by rfl⟩ : syracuseStep 1301863 = 1952795) B1952795
theorem B7036519 : Blo 1156638 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B1303519 : Blo 1156638 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B7630033 : Blo 1156638 7630033 := bstep (se 2 (by rfl) ⟨2861262, by rfl⟩ : syracuseStep 7630033 = 5722525) B5722525
theorem B75198901 : Blo 1156638 75198901 := bstep (se 5 (by rfl) ⟨3524948, by rfl⟩ : syracuseStep 75198901 = 7049897) B7049897
theorem B8910461 : Blo 1156638 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B1737983 : Blo 1156638 1737983 := bstep (se 1 (by rfl) ⟨1303487, by rfl⟩ : syracuseStep 1737983 = 2606975) B2606975
theorem B1738025 : Blo 1156638 1738025 := bstep (se 2 (by rfl) ⟨651759, by rfl⟩ : syracuseStep 1738025 = 1303519) B1303519
theorem B5940307 : Blo 1156638 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B9382025 : Blo 1156638 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B6600275 : Blo 1156638 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B10173377 : Blo 1156638 10173377 := bstep (se 2 (by rfl) ⟨3815016, by rfl⟩ : syracuseStep 10173377 = 7630033) B7630033
theorem B2605391 : Blo 1156638 2605391 := bstep (se 1 (by rfl) ⟨1954043, by rfl⟩ : syracuseStep 2605391 = 3908087) B3908087
theorem B3131731 : Blo 1156638 3131731 := bstep (se 1 (by rfl) ⟨2348798, by rfl⟩ : syracuseStep 3131731 = 4697597) B4697597
theorem B3301823 : Blo 1156638 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B1561947371 : Blo 1156638 1561947371 := bstep (se 1 (by rfl) ⟨1171460528, by rfl⟩ : syracuseStep 1561947371 = 2342921057) B2342921057
theorem B100265201 : Blo 1156638 100265201 := bstep (se 2 (by rfl) ⟨37599450, by rfl⟩ : syracuseStep 100265201 = 75198901) B75198901
theorem B1735817 : Blo 1156638 1735817 := bstep (se 2 (by rfl) ⟨650931, by rfl⟩ : syracuseStep 1735817 = 1301863) B1301863
theorem B1736927 : Blo 1156638 1736927 := bstep (se 1 (by rfl) ⟨1302695, by rfl⟩ : syracuseStep 1736927 = 2605391) B2605391
theorem B4400183 : Blo 1156638 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B1157211 : Blo 1156638 1157211 := bstep (se 1 (by rfl) ⟨867908, by rfl⟩ : syracuseStep 1157211 = 1735817) B1735817
theorem B1158655 : Blo 1156638 1158655 := bstep (se 1 (by rfl) ⟨868991, by rfl⟩ : syracuseStep 1158655 = 1737983) B1737983
theorem B1158683 : Blo 1156638 1158683 := bstep (se 1 (by rfl) ⟨869012, by rfl⟩ : syracuseStep 1158683 = 1738025) B1738025
theorem B4175641 : Blo 1156638 4175641 := bstep (se 2 (by rfl) ⟨1565865, by rfl⟩ : syracuseStep 4175641 = 3131731) B3131731
theorem B25018733 : Blo 1156638 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B8804861 : Blo 1156638 8804861 := bstep (se 3 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 8804861 = 3301823) B3301823
theorem B7920409 : Blo 1156638 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B1041298247 : Blo 1156638 1041298247 := bstep (se 1 (by rfl) ⟨780973685, by rfl⟩ : syracuseStep 1041298247 = 1561947371) B1561947371
theorem B66843467 : Blo 1156638 66843467 := bstep (se 1 (by rfl) ⟨50132600, by rfl⟩ : syracuseStep 66843467 = 100265201) B100265201
theorem B6782251 : Blo 1156638 6782251 := bstep (se 1 (by rfl) ⟨5086688, by rfl⟩ : syracuseStep 6782251 = 10173377) B10173377
theorem B16679155 : Blo 1156638 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B5869907 : Blo 1156638 5869907 := bstep (se 1 (by rfl) ⟨4402430, by rfl⟩ : syracuseStep 5869907 = 8804861) B8804861
theorem B694198831 : Blo 1156638 694198831 := bstep (se 1 (by rfl) ⟨520649123, by rfl⟩ : syracuseStep 694198831 = 1041298247) B1041298247
theorem B10560545 : Blo 1156638 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B1157951 : Blo 1156638 1157951 := bstep (se 1 (by rfl) ⟨868463, by rfl⟩ : syracuseStep 1157951 = 1736927) B1736927
theorem B2933455 : Blo 1156638 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B22270085 : Blo 1156638 22270085 := bstep (se 4 (by rfl) ⟨2087820, by rfl⟩ : syracuseStep 22270085 = 4175641) B4175641
theorem B44562311 : Blo 1156638 44562311 := bstep (se 1 (by rfl) ⟨33421733, by rfl⟩ : syracuseStep 44562311 = 66843467) B66843467
theorem B9043001 : Blo 1156638 9043001 := bstep (se 2 (by rfl) ⟨3391125, by rfl⟩ : syracuseStep 9043001 = 6782251) B6782251
theorem B925598441 : Blo 1156638 925598441 := bstep (se 2 (by rfl) ⟨347099415, by rfl⟩ : syracuseStep 925598441 = 694198831) B694198831
theorem B14846723 : Blo 1156638 14846723 := bstep (se 1 (by rfl) ⟨11135042, by rfl⟩ : syracuseStep 14846723 = 22270085) B22270085
theorem B3911273 : Blo 1156638 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B3913271 : Blo 1156638 3913271 := bstep (se 1 (by rfl) ⟨2934953, by rfl⟩ : syracuseStep 3913271 = 5869907) B5869907
theorem B29708207 : Blo 1156638 29708207 := bstep (se 1 (by rfl) ⟨22281155, by rfl⟩ : syracuseStep 29708207 = 44562311) B44562311
theorem B22238873 : Blo 1156638 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B7040363 : Blo 1156638 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B6028667 : Blo 1156638 6028667 := bstep (se 1 (by rfl) ⟨4521500, by rfl⟩ : syracuseStep 6028667 = 9043001) B9043001
theorem B9897815 : Blo 1156638 9897815 := bstep (se 1 (by rfl) ⟨7423361, by rfl⟩ : syracuseStep 9897815 = 14846723) B14846723
theorem B617065627 : Blo 1156638 617065627 := bstep (se 1 (by rfl) ⟨462799220, by rfl⟩ : syracuseStep 617065627 = 925598441) B925598441
theorem B19805471 : Blo 1156638 19805471 := bstep (se 1 (by rfl) ⟨14854103, by rfl⟩ : syracuseStep 19805471 = 29708207) B29708207
theorem B14825915 : Blo 1156638 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B2607515 : Blo 1156638 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B2608847 : Blo 1156638 2608847 := bstep (se 1 (by rfl) ⟨1956635, by rfl⟩ : syracuseStep 2608847 = 3913271) B3913271
theorem B4019111 : Blo 1156638 4019111 := bstep (se 1 (by rfl) ⟨3014333, by rfl⟩ : syracuseStep 4019111 = 6028667) B6028667
theorem B18774301 : Blo 1156638 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B1738343 : Blo 1156638 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B1739231 : Blo 1156638 1739231 := bstep (se 1 (by rfl) ⟨1304423, by rfl⟩ : syracuseStep 1739231 = 2608847) B2608847
theorem B6598543 : Blo 1156638 6598543 := bstep (se 1 (by rfl) ⟨4948907, by rfl⟩ : syracuseStep 6598543 = 9897815) B9897815
theorem B822754169 : Blo 1156638 822754169 := bstep (se 2 (by rfl) ⟨308532813, by rfl⟩ : syracuseStep 822754169 = 617065627) B617065627
theorem B9883943 : Blo 1156638 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B2679407 : Blo 1156638 2679407 := bstep (se 1 (by rfl) ⟨2009555, by rfl⟩ : syracuseStep 2679407 = 4019111) B4019111
theorem B25032401 : Blo 1156638 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B13203647 : Blo 1156638 13203647 := bstep (se 1 (by rfl) ⟨9902735, by rfl⟩ : syracuseStep 13203647 = 19805471) B19805471
theorem B6589295 : Blo 1156638 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B16688267 : Blo 1156638 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B1158895 : Blo 1156638 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B1159487 : Blo 1156638 1159487 := bstep (se 1 (by rfl) ⟨869615, by rfl⟩ : syracuseStep 1159487 = 1739231) B1739231
theorem B8798057 : Blo 1156638 8798057 := bstep (se 2 (by rfl) ⟨3299271, by rfl⟩ : syracuseStep 8798057 = 6598543) B6598543
theorem B1786271 : Blo 1156638 1786271 := bstep (se 1 (by rfl) ⟨1339703, by rfl⟩ : syracuseStep 1786271 = 2679407) B2679407
theorem B8802431 : Blo 1156638 8802431 := bstep (se 1 (by rfl) ⟨6601823, by rfl⟩ : syracuseStep 8802431 = 13203647) B13203647
theorem B548502779 : Blo 1156638 548502779 := bstep (se 1 (by rfl) ⟨411377084, by rfl⟩ : syracuseStep 548502779 = 822754169) B822754169
theorem B4392863 : Blo 1156638 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B5868287 : Blo 1156638 5868287 := bstep (se 1 (by rfl) ⟨4401215, by rfl⟩ : syracuseStep 5868287 = 8802431) B8802431
theorem B365668519 : Blo 1156638 365668519 := bstep (se 1 (by rfl) ⟨274251389, by rfl⟩ : syracuseStep 365668519 = 548502779) B548502779
theorem B4763389 : Blo 1156638 4763389 := bstep (se 3 (by rfl) ⟨893135, by rfl⟩ : syracuseStep 4763389 = 1786271) B1786271
theorem B11125511 : Blo 1156638 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B5865371 : Blo 1156638 5865371 := bstep (se 1 (by rfl) ⟨4399028, by rfl⟩ : syracuseStep 5865371 = 8798057) B8798057
theorem B487558025 : Blo 1156638 487558025 := bstep (se 2 (by rfl) ⟨182834259, by rfl⟩ : syracuseStep 487558025 = 365668519) B365668519
theorem B3910247 : Blo 1156638 3910247 := bstep (se 1 (by rfl) ⟨2932685, by rfl⟩ : syracuseStep 3910247 = 5865371) B5865371
theorem B7417007 : Blo 1156638 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B2928575 : Blo 1156638 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B3912191 : Blo 1156638 3912191 := bstep (se 1 (by rfl) ⟨2934143, by rfl⟩ : syracuseStep 3912191 = 5868287) B5868287
theorem B6351185 : Blo 1156638 6351185 := bstep (se 2 (by rfl) ⟨2381694, by rfl⟩ : syracuseStep 6351185 = 4763389) B4763389
theorem B4234123 : Blo 1156638 4234123 := bstep (se 1 (by rfl) ⟨3175592, by rfl⟩ : syracuseStep 4234123 = 6351185) B6351185
theorem B325038683 : Blo 1156638 325038683 := bstep (se 1 (by rfl) ⟨243779012, by rfl⟩ : syracuseStep 325038683 = 487558025) B487558025
theorem B2606831 : Blo 1156638 2606831 := bstep (se 1 (by rfl) ⟨1955123, by rfl⟩ : syracuseStep 2606831 = 3910247) B3910247
theorem B1952383 : Blo 1156638 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B2608127 : Blo 1156638 2608127 := bstep (se 1 (by rfl) ⟨1956095, by rfl⟩ : syracuseStep 2608127 = 3912191) B3912191
theorem B4944671 : Blo 1156638 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B1737887 : Blo 1156638 1737887 := bstep (se 1 (by rfl) ⟨1303415, by rfl⟩ : syracuseStep 1737887 = 2606831) B2606831
theorem B1738751 : Blo 1156638 1738751 := bstep (se 1 (by rfl) ⟨1304063, by rfl⟩ : syracuseStep 1738751 = 2608127) B2608127
theorem B5645497 : Blo 1156638 5645497 := bstep (se 2 (by rfl) ⟨2117061, by rfl⟩ : syracuseStep 5645497 = 4234123) B4234123
theorem B2603177 : Blo 1156638 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B3296447 : Blo 1156638 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B216692455 : Blo 1156638 216692455 := bstep (se 1 (by rfl) ⟨162519341, by rfl⟩ : syracuseStep 216692455 = 325038683) B325038683
theorem B2197631 : Blo 1156638 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B288923273 : Blo 1156638 288923273 := bstep (se 2 (by rfl) ⟨108346227, by rfl⟩ : syracuseStep 288923273 = 216692455) B216692455
theorem B1158591 : Blo 1156638 1158591 := bstep (se 1 (by rfl) ⟨868943, by rfl⟩ : syracuseStep 1158591 = 1737887) B1737887
theorem B1159167 : Blo 1156638 1159167 := bstep (se 1 (by rfl) ⟨869375, by rfl⟩ : syracuseStep 1159167 = 1738751) B1738751
theorem B7527329 : Blo 1156638 7527329 := bstep (se 2 (by rfl) ⟨2822748, by rfl⟩ : syracuseStep 7527329 = 5645497) B5645497
theorem B1735451 : Blo 1156638 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B5018219 : Blo 1156638 5018219 := bstep (se 1 (by rfl) ⟨3763664, by rfl⟩ : syracuseStep 5018219 = 7527329) B7527329
theorem B192615515 : Blo 1156638 192615515 := bstep (se 1 (by rfl) ⟨144461636, by rfl⟩ : syracuseStep 192615515 = 288923273) B288923273
theorem B1156967 : Blo 1156638 1156967 := bstep (se 1 (by rfl) ⟨867725, by rfl⟩ : syracuseStep 1156967 = 1735451) B1735451
theorem B5860349 : Blo 1156638 5860349 := bstep (se 3 (by rfl) ⟨1098815, by rfl⟩ : syracuseStep 5860349 = 2197631) B2197631
theorem B3345479 : Blo 1156638 3345479 := bstep (se 1 (by rfl) ⟨2509109, by rfl⟩ : syracuseStep 3345479 = 5018219) B5018219
theorem B3906899 : Blo 1156638 3906899 := bstep (se 1 (by rfl) ⟨2930174, by rfl⟩ : syracuseStep 3906899 = 5860349) B5860349
theorem B128410343 : Blo 1156638 128410343 := bstep (se 1 (by rfl) ⟨96307757, by rfl⟩ : syracuseStep 128410343 = 192615515) B192615515
theorem B2230319 : Blo 1156638 2230319 := bstep (se 1 (by rfl) ⟨1672739, by rfl⟩ : syracuseStep 2230319 = 3345479) B3345479
theorem B2604599 : Blo 1156638 2604599 := bstep (se 1 (by rfl) ⟨1953449, by rfl⟩ : syracuseStep 2604599 = 3906899) B3906899
theorem B85606895 : Blo 1156638 85606895 := bstep (se 1 (by rfl) ⟨64205171, by rfl⟩ : syracuseStep 85606895 = 128410343) B128410343
theorem B1486879 : Blo 1156638 1486879 := bstep (se 1 (by rfl) ⟨1115159, by rfl⟩ : syracuseStep 1486879 = 2230319) B2230319
theorem B228285053 : Blo 1156638 228285053 := bstep (se 3 (by rfl) ⟨42803447, by rfl⟩ : syracuseStep 228285053 = 85606895) B85606895
theorem B1736399 : Blo 1156638 1736399 := bstep (se 1 (by rfl) ⟨1302299, by rfl⟩ : syracuseStep 1736399 = 2604599) B2604599
theorem B7930021 : Blo 1156638 7930021 := bstep (se 4 (by rfl) ⟨743439, by rfl⟩ : syracuseStep 7930021 = 1486879) B1486879
theorem B1157599 : Blo 1156638 1157599 := bstep (se 1 (by rfl) ⟨868199, by rfl⟩ : syracuseStep 1157599 = 1736399) B1736399
theorem B152190035 : Blo 1156638 152190035 := bstep (se 1 (by rfl) ⟨114142526, by rfl⟩ : syracuseStep 152190035 = 228285053) B228285053
theorem B101460023 : Blo 1156638 101460023 := bstep (se 1 (by rfl) ⟨76095017, by rfl⟩ : syracuseStep 101460023 = 152190035) B152190035
theorem B10573361 : Blo 1156638 10573361 := bstep (se 2 (by rfl) ⟨3965010, by rfl⟩ : syracuseStep 10573361 = 7930021) B7930021
theorem B7048907 : Blo 1156638 7048907 := bstep (se 1 (by rfl) ⟨5286680, by rfl⟩ : syracuseStep 7048907 = 10573361) B10573361
theorem B67640015 : Blo 1156638 67640015 := bstep (se 1 (by rfl) ⟨50730011, by rfl⟩ : syracuseStep 67640015 = 101460023) B101460023
theorem B45093343 : Blo 1156638 45093343 := bstep (se 1 (by rfl) ⟨33820007, by rfl⟩ : syracuseStep 45093343 = 67640015) B67640015
theorem B4699271 : Blo 1156638 4699271 := bstep (se 1 (by rfl) ⟨3524453, by rfl⟩ : syracuseStep 4699271 = 7048907) B7048907
theorem B3132847 : Blo 1156638 3132847 := bstep (se 1 (by rfl) ⟨2349635, by rfl⟩ : syracuseStep 3132847 = 4699271) B4699271
theorem B60124457 : Blo 1156638 60124457 := bstep (se 2 (by rfl) ⟨22546671, by rfl⟩ : syracuseStep 60124457 = 45093343) B45093343
theorem B40082971 : Blo 1156638 40082971 := bstep (se 1 (by rfl) ⟨30062228, by rfl⟩ : syracuseStep 40082971 = 60124457) B60124457
theorem B4177129 : Blo 1156638 4177129 := bstep (se 2 (by rfl) ⟨1566423, by rfl⟩ : syracuseStep 4177129 = 3132847) B3132847
theorem B5569505 : Blo 1156638 5569505 := bstep (se 2 (by rfl) ⟨2088564, by rfl⟩ : syracuseStep 5569505 = 4177129) B4177129
theorem B53443961 : Blo 1156638 53443961 := bstep (se 2 (by rfl) ⟨20041485, by rfl⟩ : syracuseStep 53443961 = 40082971) B40082971
theorem B3713003 : Blo 1156638 3713003 := bstep (se 1 (by rfl) ⟨2784752, by rfl⟩ : syracuseStep 3713003 = 5569505) B5569505
theorem B35629307 : Blo 1156638 35629307 := bstep (se 1 (by rfl) ⟨26721980, by rfl⟩ : syracuseStep 35629307 = 53443961) B53443961
theorem B2475335 : Blo 1156638 2475335 := bstep (se 1 (by rfl) ⟨1856501, by rfl⟩ : syracuseStep 2475335 = 3713003) B3713003
theorem B23752871 : Blo 1156638 23752871 := bstep (se 1 (by rfl) ⟨17814653, by rfl⟩ : syracuseStep 23752871 = 35629307) B35629307
theorem B15835247 : Blo 1156638 15835247 := bstep (se 1 (by rfl) ⟨11876435, by rfl⟩ : syracuseStep 15835247 = 23752871) B23752871
theorem B1650223 : Blo 1156638 1650223 := bstep (se 1 (by rfl) ⟨1237667, by rfl⟩ : syracuseStep 1650223 = 2475335) B2475335
theorem B2200297 : Blo 1156638 2200297 := bstep (se 2 (by rfl) ⟨825111, by rfl⟩ : syracuseStep 2200297 = 1650223) B1650223
theorem B10556831 : Blo 1156638 10556831 := bstep (se 1 (by rfl) ⟨7917623, by rfl⟩ : syracuseStep 10556831 = 15835247) B15835247
theorem B2933729 : Blo 1156638 2933729 := bstep (se 2 (by rfl) ⟨1100148, by rfl⟩ : syracuseStep 2933729 = 2200297) B2200297
theorem B7037887 : Blo 1156638 7037887 := bstep (se 1 (by rfl) ⟨5278415, by rfl⟩ : syracuseStep 7037887 = 10556831) B10556831
theorem B9383849 : Blo 1156638 9383849 := bstep (se 2 (by rfl) ⟨3518943, by rfl⟩ : syracuseStep 9383849 = 7037887) B7037887
theorem B1955819 : Blo 1156638 1955819 := bstep (se 1 (by rfl) ⟨1466864, by rfl⟩ : syracuseStep 1955819 = 2933729) B2933729
theorem B1303879 : Blo 1156638 1303879 := bstep (se 1 (by rfl) ⟨977909, by rfl⟩ : syracuseStep 1303879 = 1955819) B1955819
theorem B6255899 : Blo 1156638 6255899 := bstep (se 1 (by rfl) ⟨4691924, by rfl⟩ : syracuseStep 6255899 = 9383849) B9383849
theorem B1738505 : Blo 1156638 1738505 := bstep (se 2 (by rfl) ⟨651939, by rfl⟩ : syracuseStep 1738505 = 1303879) B1303879
theorem B4170599 : Blo 1156638 4170599 := bstep (se 1 (by rfl) ⟨3127949, by rfl⟩ : syracuseStep 4170599 = 6255899) B6255899
theorem B1159003 : Blo 1156638 1159003 := bstep (se 1 (by rfl) ⟨869252, by rfl⟩ : syracuseStep 1159003 = 1738505) B1738505
theorem B2780399 : Blo 1156638 2780399 := bstep (se 1 (by rfl) ⟨2085299, by rfl⟩ : syracuseStep 2780399 = 4170599) B4170599
theorem B1853599 : Blo 1156638 1853599 := bstep (se 1 (by rfl) ⟨1390199, by rfl⟩ : syracuseStep 1853599 = 2780399) B2780399
theorem B2471465 : Blo 1156638 2471465 := bstep (se 2 (by rfl) ⟨926799, by rfl⟩ : syracuseStep 2471465 = 1853599) B1853599
theorem B1647643 : Blo 1156638 1647643 := bstep (se 1 (by rfl) ⟨1235732, by rfl⟩ : syracuseStep 1647643 = 2471465) B2471465
theorem B2196857 : Blo 1156638 2196857 := bstep (se 2 (by rfl) ⟨823821, by rfl⟩ : syracuseStep 2196857 = 1647643) B1647643
theorem B1464571 : Blo 1156638 1464571 := bstep (se 1 (by rfl) ⟨1098428, by rfl⟩ : syracuseStep 1464571 = 2196857) B2196857
theorem B1952761 : Blo 1156638 1952761 := bstep (se 2 (by rfl) ⟨732285, by rfl⟩ : syracuseStep 1952761 = 1464571) B1464571
theorem B2603681 : Blo 1156638 2603681 := bstep (se 2 (by rfl) ⟨976380, by rfl⟩ : syracuseStep 2603681 = 1952761) B1952761
theorem B1735787 : Blo 1156638 1735787 := bstep (se 1 (by rfl) ⟨1301840, by rfl⟩ : syracuseStep 1735787 = 2603681) B2603681
theorem B1157191 : Blo 1156638 1157191 := bstep (se 1 (by rfl) ⟨867893, by rfl⟩ : syracuseStep 1157191 = 1735787) B1735787

theorem C0 (j : ℕ) (h1 : 289159 ≤ j) (h2 : j ≤ 289858) : Blo 1156638 (4 * j + 3) := by
  interval_cases j
  · exact B1156639
  · exact B1156643
  · exact B1156647
  · exact B1156651
  · exact B1156655
  · exact B1156659
  · exact B1156663
  · exact B1156667
  · exact B1156671
  · exact B1156675
  · exact B1156679
  · exact B1156683
  · exact B1156687
  · exact B1156691
  · exact B1156695
  · exact B1156699
  · exact B1156703
  · exact B1156707
  · exact B1156711
  · exact B1156715
  · exact B1156719
  · exact B1156723
  · exact B1156727
  · exact B1156731
  · exact B1156735
  · exact B1156739
  · exact B1156743
  · exact B1156747
  · exact B1156751
  · exact B1156755
  · exact B1156759
  · exact B1156763
  · exact B1156767
  · exact B1156771
  · exact B1156775
  · exact B1156779
  · exact B1156783
  · exact B1156787
  · exact B1156791
  · exact B1156795
  · exact B1156799
  · exact B1156803
  · exact B1156807
  · exact B1156811
  · exact B1156815
  · exact B1156819
  · exact B1156823
  · exact B1156827
  · exact B1156831
  · exact B1156835
  · exact B1156839
  · exact B1156843
  · exact B1156847
  · exact B1156851
  · exact B1156855
  · exact B1156859
  · exact B1156863
  · exact B1156867
  · exact B1156871
  · exact B1156875
  · exact B1156879
  · exact B1156883
  · exact B1156887
  · exact B1156891
  · exact B1156895
  · exact B1156899
  · exact B1156903
  · exact B1156907
  · exact B1156911
  · exact B1156915
  · exact B1156919
  · exact B1156923
  · exact B1156927
  · exact B1156931
  · exact B1156935
  · exact B1156939
  · exact B1156943
  · exact B1156947
  · exact B1156951
  · exact B1156955
  · exact B1156959
  · exact B1156963
  · exact B1156967
  · exact B1156971
  · exact B1156975
  · exact B1156979
  · exact B1156983
  · exact B1156987
  · exact B1156991
  · exact B1156995
  · exact B1156999
  · exact B1157003
  · exact B1157007
  · exact B1157011
  · exact B1157015
  · exact B1157019
  · exact B1157023
  · exact B1157027
  · exact B1157031
  · exact B1157035
  · exact B1157039
  · exact B1157043
  · exact B1157047
  · exact B1157051
  · exact B1157055
  · exact B1157059
  · exact B1157063
  · exact B1157067
  · exact B1157071
  · exact B1157075
  · exact B1157079
  · exact B1157083
  · exact B1157087
  · exact B1157091
  · exact B1157095
  · exact B1157099
  · exact B1157103
  · exact B1157107
  · exact B1157111
  · exact B1157115
  · exact B1157119
  · exact B1157123
  · exact B1157127
  · exact B1157131
  · exact B1157135
  · exact B1157139
  · exact B1157143
  · exact B1157147
  · exact B1157151
  · exact B1157155
  · exact B1157159
  · exact B1157163
  · exact B1157167
  · exact B1157171
  · exact B1157175
  · exact B1157179
  · exact B1157183
  · exact B1157187
  · exact B1157191
  · exact B1157195
  · exact B1157199
  · exact B1157203
  · exact B1157207
  · exact B1157211
  · exact B1157215
  · exact B1157219
  · exact B1157223
  · exact B1157227
  · exact B1157231
  · exact B1157235
  · exact B1157239
  · exact B1157243
  · exact B1157247
  · exact B1157251
  · exact B1157255
  · exact B1157259
  · exact B1157263
  · exact B1157267
  · exact B1157271
  · exact B1157275
  · exact B1157279
  · exact B1157283
  · exact B1157287
  · exact B1157291
  · exact B1157295
  · exact B1157299
  · exact B1157303
  · exact B1157307
  · exact B1157311
  · exact B1157315
  · exact B1157319
  · exact B1157323
  · exact B1157327
  · exact B1157331
  · exact B1157335
  · exact B1157339
  · exact B1157343
  · exact B1157347
  · exact B1157351
  · exact B1157355
  · exact B1157359
  · exact B1157363
  · exact B1157367
  · exact B1157371
  · exact B1157375
  · exact B1157379
  · exact B1157383
  · exact B1157387
  · exact B1157391
  · exact B1157395
  · exact B1157399
  · exact B1157403
  · exact B1157407
  · exact B1157411
  · exact B1157415
  · exact B1157419
  · exact B1157423
  · exact B1157427
  · exact B1157431
  · exact B1157435
  · exact B1157439
  · exact B1157443
  · exact B1157447
  · exact B1157451
  · exact B1157455
  · exact B1157459
  · exact B1157463
  · exact B1157467
  · exact B1157471
  · exact B1157475
  · exact B1157479
  · exact B1157483
  · exact B1157487
  · exact B1157491
  · exact B1157495
  · exact B1157499
  · exact B1157503
  · exact B1157507
  · exact B1157511
  · exact B1157515
  · exact B1157519
  · exact B1157523
  · exact B1157527
  · exact B1157531
  · exact B1157535
  · exact B1157539
  · exact B1157543
  · exact B1157547
  · exact B1157551
  · exact B1157555
  · exact B1157559
  · exact B1157563
  · exact B1157567
  · exact B1157571
  · exact B1157575
  · exact B1157579
  · exact B1157583
  · exact B1157587
  · exact B1157591
  · exact B1157595
  · exact B1157599
  · exact B1157603
  · exact B1157607
  · exact B1157611
  · exact B1157615
  · exact B1157619
  · exact B1157623
  · exact B1157627
  · exact B1157631
  · exact B1157635
  · exact B1157639
  · exact B1157643
  · exact B1157647
  · exact B1157651
  · exact B1157655
  · exact B1157659
  · exact B1157663
  · exact B1157667
  · exact B1157671
  · exact B1157675
  · exact B1157679
  · exact B1157683
  · exact B1157687
  · exact B1157691
  · exact B1157695
  · exact B1157699
  · exact B1157703
  · exact B1157707
  · exact B1157711
  · exact B1157715
  · exact B1157719
  · exact B1157723
  · exact B1157727
  · exact B1157731
  · exact B1157735
  · exact B1157739
  · exact B1157743
  · exact B1157747
  · exact B1157751
  · exact B1157755
  · exact B1157759
  · exact B1157763
  · exact B1157767
  · exact B1157771
  · exact B1157775
  · exact B1157779
  · exact B1157783
  · exact B1157787
  · exact B1157791
  · exact B1157795
  · exact B1157799
  · exact B1157803
  · exact B1157807
  · exact B1157811
  · exact B1157815
  · exact B1157819
  · exact B1157823
  · exact B1157827
  · exact B1157831
  · exact B1157835
  · exact B1157839
  · exact B1157843
  · exact B1157847
  · exact B1157851
  · exact B1157855
  · exact B1157859
  · exact B1157863
  · exact B1157867
  · exact B1157871
  · exact B1157875
  · exact B1157879
  · exact B1157883
  · exact B1157887
  · exact B1157891
  · exact B1157895
  · exact B1157899
  · exact B1157903
  · exact B1157907
  · exact B1157911
  · exact B1157915
  · exact B1157919
  · exact B1157923
  · exact B1157927
  · exact B1157931
  · exact B1157935
  · exact B1157939
  · exact B1157943
  · exact B1157947
  · exact B1157951
  · exact B1157955
  · exact B1157959
  · exact B1157963
  · exact B1157967
  · exact B1157971
  · exact B1157975
  · exact B1157979
  · exact B1157983
  · exact B1157987
  · exact B1157991
  · exact B1157995
  · exact B1157999
  · exact B1158003
  · exact B1158007
  · exact B1158011
  · exact B1158015
  · exact B1158019
  · exact B1158023
  · exact B1158027
  · exact B1158031
  · exact B1158035
  · exact B1158039
  · exact B1158043
  · exact B1158047
  · exact B1158051
  · exact B1158055
  · exact B1158059
  · exact B1158063
  · exact B1158067
  · exact B1158071
  · exact B1158075
  · exact B1158079
  · exact B1158083
  · exact B1158087
  · exact B1158091
  · exact B1158095
  · exact B1158099
  · exact B1158103
  · exact B1158107
  · exact B1158111
  · exact B1158115
  · exact B1158119
  · exact B1158123
  · exact B1158127
  · exact B1158131
  · exact B1158135
  · exact B1158139
  · exact B1158143
  · exact B1158147
  · exact B1158151
  · exact B1158155
  · exact B1158159
  · exact B1158163
  · exact B1158167
  · exact B1158171
  · exact B1158175
  · exact B1158179
  · exact B1158183
  · exact B1158187
  · exact B1158191
  · exact B1158195
  · exact B1158199
  · exact B1158203
  · exact B1158207
  · exact B1158211
  · exact B1158215
  · exact B1158219
  · exact B1158223
  · exact B1158227
  · exact B1158231
  · exact B1158235
  · exact B1158239
  · exact B1158243
  · exact B1158247
  · exact B1158251
  · exact B1158255
  · exact B1158259
  · exact B1158263
  · exact B1158267
  · exact B1158271
  · exact B1158275
  · exact B1158279
  · exact B1158283
  · exact B1158287
  · exact B1158291
  · exact B1158295
  · exact B1158299
  · exact B1158303
  · exact B1158307
  · exact B1158311
  · exact B1158315
  · exact B1158319
  · exact B1158323
  · exact B1158327
  · exact B1158331
  · exact B1158335
  · exact B1158339
  · exact B1158343
  · exact B1158347
  · exact B1158351
  · exact B1158355
  · exact B1158359
  · exact B1158363
  · exact B1158367
  · exact B1158371
  · exact B1158375
  · exact B1158379
  · exact B1158383
  · exact B1158387
  · exact B1158391
  · exact B1158395
  · exact B1158399
  · exact B1158403
  · exact B1158407
  · exact B1158411
  · exact B1158415
  · exact B1158419
  · exact B1158423
  · exact B1158427
  · exact B1158431
  · exact B1158435
  · exact B1158439
  · exact B1158443
  · exact B1158447
  · exact B1158451
  · exact B1158455
  · exact B1158459
  · exact B1158463
  · exact B1158467
  · exact B1158471
  · exact B1158475
  · exact B1158479
  · exact B1158483
  · exact B1158487
  · exact B1158491
  · exact B1158495
  · exact B1158499
  · exact B1158503
  · exact B1158507
  · exact B1158511
  · exact B1158515
  · exact B1158519
  · exact B1158523
  · exact B1158527
  · exact B1158531
  · exact B1158535
  · exact B1158539
  · exact B1158543
  · exact B1158547
  · exact B1158551
  · exact B1158555
  · exact B1158559
  · exact B1158563
  · exact B1158567
  · exact B1158571
  · exact B1158575
  · exact B1158579
  · exact B1158583
  · exact B1158587
  · exact B1158591
  · exact B1158595
  · exact B1158599
  · exact B1158603
  · exact B1158607
  · exact B1158611
  · exact B1158615
  · exact B1158619
  · exact B1158623
  · exact B1158627
  · exact B1158631
  · exact B1158635
  · exact B1158639
  · exact B1158643
  · exact B1158647
  · exact B1158651
  · exact B1158655
  · exact B1158659
  · exact B1158663
  · exact B1158667
  · exact B1158671
  · exact B1158675
  · exact B1158679
  · exact B1158683
  · exact B1158687
  · exact B1158691
  · exact B1158695
  · exact B1158699
  · exact B1158703
  · exact B1158707
  · exact B1158711
  · exact B1158715
  · exact B1158719
  · exact B1158723
  · exact B1158727
  · exact B1158731
  · exact B1158735
  · exact B1158739
  · exact B1158743
  · exact B1158747
  · exact B1158751
  · exact B1158755
  · exact B1158759
  · exact B1158763
  · exact B1158767
  · exact B1158771
  · exact B1158775
  · exact B1158779
  · exact B1158783
  · exact B1158787
  · exact B1158791
  · exact B1158795
  · exact B1158799
  · exact B1158803
  · exact B1158807
  · exact B1158811
  · exact B1158815
  · exact B1158819
  · exact B1158823
  · exact B1158827
  · exact B1158831
  · exact B1158835
  · exact B1158839
  · exact B1158843
  · exact B1158847
  · exact B1158851
  · exact B1158855
  · exact B1158859
  · exact B1158863
  · exact B1158867
  · exact B1158871
  · exact B1158875
  · exact B1158879
  · exact B1158883
  · exact B1158887
  · exact B1158891
  · exact B1158895
  · exact B1158899
  · exact B1158903
  · exact B1158907
  · exact B1158911
  · exact B1158915
  · exact B1158919
  · exact B1158923
  · exact B1158927
  · exact B1158931
  · exact B1158935
  · exact B1158939
  · exact B1158943
  · exact B1158947
  · exact B1158951
  · exact B1158955
  · exact B1158959
  · exact B1158963
  · exact B1158967
  · exact B1158971
  · exact B1158975
  · exact B1158979
  · exact B1158983
  · exact B1158987
  · exact B1158991
  · exact B1158995
  · exact B1158999
  · exact B1159003
  · exact B1159007
  · exact B1159011
  · exact B1159015
  · exact B1159019
  · exact B1159023
  · exact B1159027
  · exact B1159031
  · exact B1159035
  · exact B1159039
  · exact B1159043
  · exact B1159047
  · exact B1159051
  · exact B1159055
  · exact B1159059
  · exact B1159063
  · exact B1159067
  · exact B1159071
  · exact B1159075
  · exact B1159079
  · exact B1159083
  · exact B1159087
  · exact B1159091
  · exact B1159095
  · exact B1159099
  · exact B1159103
  · exact B1159107
  · exact B1159111
  · exact B1159115
  · exact B1159119
  · exact B1159123
  · exact B1159127
  · exact B1159131
  · exact B1159135
  · exact B1159139
  · exact B1159143
  · exact B1159147
  · exact B1159151
  · exact B1159155
  · exact B1159159
  · exact B1159163
  · exact B1159167
  · exact B1159171
  · exact B1159175
  · exact B1159179
  · exact B1159183
  · exact B1159187
  · exact B1159191
  · exact B1159195
  · exact B1159199
  · exact B1159203
  · exact B1159207
  · exact B1159211
  · exact B1159215
  · exact B1159219
  · exact B1159223
  · exact B1159227
  · exact B1159231
  · exact B1159235
  · exact B1159239
  · exact B1159243
  · exact B1159247
  · exact B1159251
  · exact B1159255
  · exact B1159259
  · exact B1159263
  · exact B1159267
  · exact B1159271
  · exact B1159275
  · exact B1159279
  · exact B1159283
  · exact B1159287
  · exact B1159291
  · exact B1159295
  · exact B1159299
  · exact B1159303
  · exact B1159307
  · exact B1159311
  · exact B1159315
  · exact B1159319
  · exact B1159323
  · exact B1159327
  · exact B1159331
  · exact B1159335
  · exact B1159339
  · exact B1159343
  · exact B1159347
  · exact B1159351
  · exact B1159355
  · exact B1159359
  · exact B1159363
  · exact B1159367
  · exact B1159371
  · exact B1159375
  · exact B1159379
  · exact B1159383
  · exact B1159387
  · exact B1159391
  · exact B1159395
  · exact B1159399
  · exact B1159403
  · exact B1159407
  · exact B1159411
  · exact B1159415
  · exact B1159419
  · exact B1159423
  · exact B1159427
  · exact B1159431
  · exact B1159435

theorem C1 (j : ℕ) (h1 : 289859 ≤ j) (h2 : j ≤ 290158) : Blo 1156638 (4 * j + 3) := by
  interval_cases j
  · exact B1159439
  · exact B1159443
  · exact B1159447
  · exact B1159451
  · exact B1159455
  · exact B1159459
  · exact B1159463
  · exact B1159467
  · exact B1159471
  · exact B1159475
  · exact B1159479
  · exact B1159483
  · exact B1159487
  · exact B1159491
  · exact B1159495
  · exact B1159499
  · exact B1159503
  · exact B1159507
  · exact B1159511
  · exact B1159515
  · exact B1159519
  · exact B1159523
  · exact B1159527
  · exact B1159531
  · exact B1159535
  · exact B1159539
  · exact B1159543
  · exact B1159547
  · exact B1159551
  · exact B1159555
  · exact B1159559
  · exact B1159563
  · exact B1159567
  · exact B1159571
  · exact B1159575
  · exact B1159579
  · exact B1159583
  · exact B1159587
  · exact B1159591
  · exact B1159595
  · exact B1159599
  · exact B1159603
  · exact B1159607
  · exact B1159611
  · exact B1159615
  · exact B1159619
  · exact B1159623
  · exact B1159627
  · exact B1159631
  · exact B1159635
  · exact B1159639
  · exact B1159643
  · exact B1159647
  · exact B1159651
  · exact B1159655
  · exact B1159659
  · exact B1159663
  · exact B1159667
  · exact B1159671
  · exact B1159675
  · exact B1159679
  · exact B1159683
  · exact B1159687
  · exact B1159691
  · exact B1159695
  · exact B1159699
  · exact B1159703
  · exact B1159707
  · exact B1159711
  · exact B1159715
  · exact B1159719
  · exact B1159723
  · exact B1159727
  · exact B1159731
  · exact B1159735
  · exact B1159739
  · exact B1159743
  · exact B1159747
  · exact B1159751
  · exact B1159755
  · exact B1159759
  · exact B1159763
  · exact B1159767
  · exact B1159771
  · exact B1159775
  · exact B1159779
  · exact B1159783
  · exact B1159787
  · exact B1159791
  · exact B1159795
  · exact B1159799
  · exact B1159803
  · exact B1159807
  · exact B1159811
  · exact B1159815
  · exact B1159819
  · exact B1159823
  · exact B1159827
  · exact B1159831
  · exact B1159835
  · exact B1159839
  · exact B1159843
  · exact B1159847
  · exact B1159851
  · exact B1159855
  · exact B1159859
  · exact B1159863
  · exact B1159867
  · exact B1159871
  · exact B1159875
  · exact B1159879
  · exact B1159883
  · exact B1159887
  · exact B1159891
  · exact B1159895
  · exact B1159899
  · exact B1159903
  · exact B1159907
  · exact B1159911
  · exact B1159915
  · exact B1159919
  · exact B1159923
  · exact B1159927
  · exact B1159931
  · exact B1159935
  · exact B1159939
  · exact B1159943
  · exact B1159947
  · exact B1159951
  · exact B1159955
  · exact B1159959
  · exact B1159963
  · exact B1159967
  · exact B1159971
  · exact B1159975
  · exact B1159979
  · exact B1159983
  · exact B1159987
  · exact B1159991
  · exact B1159995
  · exact B1159999
  · exact B1160003
  · exact B1160007
  · exact B1160011
  · exact B1160015
  · exact B1160019
  · exact B1160023
  · exact B1160027
  · exact B1160031
  · exact B1160035
  · exact B1160039
  · exact B1160043
  · exact B1160047
  · exact B1160051
  · exact B1160055
  · exact B1160059
  · exact B1160063
  · exact B1160067
  · exact B1160071
  · exact B1160075
  · exact B1160079
  · exact B1160083
  · exact B1160087
  · exact B1160091
  · exact B1160095
  · exact B1160099
  · exact B1160103
  · exact B1160107
  · exact B1160111
  · exact B1160115
  · exact B1160119
  · exact B1160123
  · exact B1160127
  · exact B1160131
  · exact B1160135
  · exact B1160139
  · exact B1160143
  · exact B1160147
  · exact B1160151
  · exact B1160155
  · exact B1160159
  · exact B1160163
  · exact B1160167
  · exact B1160171
  · exact B1160175
  · exact B1160179
  · exact B1160183
  · exact B1160187
  · exact B1160191
  · exact B1160195
  · exact B1160199
  · exact B1160203
  · exact B1160207
  · exact B1160211
  · exact B1160215
  · exact B1160219
  · exact B1160223
  · exact B1160227
  · exact B1160231
  · exact B1160235
  · exact B1160239
  · exact B1160243
  · exact B1160247
  · exact B1160251
  · exact B1160255
  · exact B1160259
  · exact B1160263
  · exact B1160267
  · exact B1160271
  · exact B1160275
  · exact B1160279
  · exact B1160283
  · exact B1160287
  · exact B1160291
  · exact B1160295
  · exact B1160299
  · exact B1160303
  · exact B1160307
  · exact B1160311
  · exact B1160315
  · exact B1160319
  · exact B1160323
  · exact B1160327
  · exact B1160331
  · exact B1160335
  · exact B1160339
  · exact B1160343
  · exact B1160347
  · exact B1160351
  · exact B1160355
  · exact B1160359
  · exact B1160363
  · exact B1160367
  · exact B1160371
  · exact B1160375
  · exact B1160379
  · exact B1160383
  · exact B1160387
  · exact B1160391
  · exact B1160395
  · exact B1160399
  · exact B1160403
  · exact B1160407
  · exact B1160411
  · exact B1160415
  · exact B1160419
  · exact B1160423
  · exact B1160427
  · exact B1160431
  · exact B1160435
  · exact B1160439
  · exact B1160443
  · exact B1160447
  · exact B1160451
  · exact B1160455
  · exact B1160459
  · exact B1160463
  · exact B1160467
  · exact B1160471
  · exact B1160475
  · exact B1160479
  · exact B1160483
  · exact B1160487
  · exact B1160491
  · exact B1160495
  · exact B1160499
  · exact B1160503
  · exact B1160507
  · exact B1160511
  · exact B1160515
  · exact B1160519
  · exact B1160523
  · exact B1160527
  · exact B1160531
  · exact B1160535
  · exact B1160539
  · exact B1160543
  · exact B1160547
  · exact B1160551
  · exact B1160555
  · exact B1160559
  · exact B1160563
  · exact B1160567
  · exact B1160571
  · exact B1160575
  · exact B1160579
  · exact B1160583
  · exact B1160587
  · exact B1160591
  · exact B1160595
  · exact B1160599
  · exact B1160603
  · exact B1160607
  · exact B1160611
  · exact B1160615
  · exact B1160619
  · exact B1160623
  · exact B1160627
  · exact B1160631
  · exact B1160635

theorem solution (m : ℕ) (hlo : 1156638 ≤ m) (hhi : m ≤ 1160638) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 289159 ≤ j := by omega
    have hj2 : j ≤ 290158 := by omega
    have hb : Blo 1156638 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 289859 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
