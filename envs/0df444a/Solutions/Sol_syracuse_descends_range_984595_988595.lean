-- Prove2me | solution 1 for syracuse_descends_range_984595_988595
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:09.307185+00:00
-- url     : https://prove2.me/submissions/a11858a8-34bd-429b-acad-e3c8469b089b

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


theorem B3801269 : Blo 984595 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B7798997 : Blo 984595 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B7111253 : Blo 984595 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B1999709 : Blo 984595 1999709 := bbase (se 3 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 1999709 = 749891) (by norm_num)
theorem B1246205 : Blo 984595 1246205 := bbase (se 3 (by rfl) ⟨233663, by rfl⟩ : syracuseStep 1246205 = 467327) (by norm_num)
theorem B1246261 : Blo 984595 1246261 := bbase (se 5 (by rfl) ⟨58418, by rfl⟩ : syracuseStep 1246261 = 116837) (by norm_num)
theorem B1246357 : Blo 984595 1246357 := bbase (se 6 (by rfl) ⟨29211, by rfl⟩ : syracuseStep 1246357 = 58423) (by norm_num)
theorem B6325397 : Blo 984595 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B3802405 : Blo 984595 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B1246529 : Blo 984595 1246529 := bbase (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) (by norm_num)
theorem B1246585 : Blo 984595 1246585 := bbase (se 2 (by rfl) ⟨467469, by rfl⟩ : syracuseStep 1246585 = 934939) (by norm_num)
theorem B1246681 : Blo 984595 1246681 := bbase (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) (by norm_num)
theorem B1869293 : Blo 984595 1869293 := bbase (se 3 (by rfl) ⟨350492, by rfl⟩ : syracuseStep 1869293 = 700985) (by norm_num)
theorem B1246853 : Blo 984595 1246853 := bbase (se 4 (by rfl) ⟨116892, by rfl⟩ : syracuseStep 1246853 = 233785) (by norm_num)
theorem B1246909 : Blo 984595 1246909 := bbase (se 3 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 1246909 = 467591) (by norm_num)
theorem B1869581 : Blo 984595 1869581 := bbase (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) (by norm_num)
theorem B1247005 : Blo 984595 1247005 := bbase (se 3 (by rfl) ⟨233813, by rfl⟩ : syracuseStep 1247005 = 467627) (by norm_num)
theorem B9471829 : Blo 984595 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B2492309 : Blo 984595 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B1869733 : Blo 984595 1869733 := bbase (se 4 (by rfl) ⟨175287, by rfl⟩ : syracuseStep 1869733 = 350575) (by norm_num)
theorem B1247177 : Blo 984595 1247177 := bbase (se 2 (by rfl) ⟨467691, by rfl⟩ : syracuseStep 1247177 = 935383) (by norm_num)
theorem B1247233 : Blo 984595 1247233 := bbase (se 2 (by rfl) ⟨467712, by rfl⟩ : syracuseStep 1247233 = 935425) (by norm_num)
theorem B4556837 : Blo 984595 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B1247329 : Blo 984595 1247329 := bbase (se 2 (by rfl) ⟨467748, by rfl⟩ : syracuseStep 1247329 = 935497) (by norm_num)
theorem B1870037 : Blo 984595 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B2492653 : Blo 984595 2492653 := bbase (se 3 (by rfl) ⟨467372, by rfl⟩ : syracuseStep 2492653 = 934745) (by norm_num)
theorem B1247501 : Blo 984595 1247501 := bbase (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) (by norm_num)
theorem B1476893 : Blo 984595 1476893 := bbase (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) (by norm_num)
theorem B1476917 : Blo 984595 1476917 := bbase (se 5 (by rfl) ⟨69230, by rfl⟩ : syracuseStep 1476917 = 138461) (by norm_num)
theorem B1247557 : Blo 984595 1247557 := bbase (se 4 (by rfl) ⟨116958, by rfl⟩ : syracuseStep 1247557 = 233917) (by norm_num)
theorem B1476941 : Blo 984595 1476941 := bbase (se 3 (by rfl) ⟨276926, by rfl⟩ : syracuseStep 1476941 = 553853) (by norm_num)
theorem B2492765 : Blo 984595 2492765 := bbase (se 3 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 2492765 = 934787) (by norm_num)
theorem B1476965 : Blo 984595 1476965 := bbase (se 4 (by rfl) ⟨138465, by rfl⟩ : syracuseStep 1476965 = 276931) (by norm_num)
theorem B1476989 : Blo 984595 1476989 := bbase (se 3 (by rfl) ⟨276935, by rfl⟩ : syracuseStep 1476989 = 553871) (by norm_num)
theorem B1477013 : Blo 984595 1477013 := bbase (se 6 (by rfl) ⟨34617, by rfl⟩ : syracuseStep 1477013 = 69235) (by norm_num)
theorem B1247653 : Blo 984595 1247653 := bbase (se 4 (by rfl) ⟨116967, by rfl⟩ : syracuseStep 1247653 = 233935) (by norm_num)
theorem B1477037 : Blo 984595 1477037 := bbase (se 3 (by rfl) ⟨276944, by rfl⟩ : syracuseStep 1477037 = 553889) (by norm_num)
theorem B1477061 : Blo 984595 1477061 := bbase (se 4 (by rfl) ⟨138474, by rfl⟩ : syracuseStep 1477061 = 276949) (by norm_num)
theorem B1477085 : Blo 984595 1477085 := bbase (se 3 (by rfl) ⟨276953, by rfl⟩ : syracuseStep 1477085 = 553907) (by norm_num)
theorem B1477109 : Blo 984595 1477109 := bbase (se 5 (by rfl) ⟨69239, by rfl⟩ : syracuseStep 1477109 = 138479) (by norm_num)
theorem B1477133 : Blo 984595 1477133 := bbase (se 3 (by rfl) ⟨276962, by rfl⟩ : syracuseStep 1477133 = 553925) (by norm_num)
theorem B2492957 : Blo 984595 2492957 := bbase (se 3 (by rfl) ⟨467429, by rfl⟩ : syracuseStep 2492957 = 934859) (by norm_num)
theorem B1477157 : Blo 984595 1477157 := bbase (se 4 (by rfl) ⟨138483, by rfl⟩ : syracuseStep 1477157 = 276967) (by norm_num)
theorem B1477181 : Blo 984595 1477181 := bbase (se 3 (by rfl) ⟨276971, by rfl⟩ : syracuseStep 1477181 = 553943) (by norm_num)
theorem B1247825 : Blo 984595 1247825 := bbase (se 2 (by rfl) ⟨467934, by rfl⟩ : syracuseStep 1247825 = 935869) (by norm_num)
theorem B1477205 : Blo 984595 1477205 := bbase (se 8 (by rfl) ⟨8655, by rfl⟩ : syracuseStep 1477205 = 17311) (by norm_num)
theorem B1477229 : Blo 984595 1477229 := bbase (se 3 (by rfl) ⟨276980, by rfl⟩ : syracuseStep 1477229 = 553961) (by norm_num)
theorem B1477253 : Blo 984595 1477253 := bbase (se 4 (by rfl) ⟨138492, by rfl⟩ : syracuseStep 1477253 = 276985) (by norm_num)
theorem B1247881 : Blo 984595 1247881 := bbase (se 2 (by rfl) ⟨467955, by rfl⟩ : syracuseStep 1247881 = 935911) (by norm_num)
theorem B1477277 : Blo 984595 1477277 := bbase (se 3 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 1477277 = 553979) (by norm_num)
theorem B1477301 : Blo 984595 1477301 := bbase (se 5 (by rfl) ⟨69248, by rfl⟩ : syracuseStep 1477301 = 138497) (by norm_num)
theorem B1477325 : Blo 984595 1477325 := bbase (se 3 (by rfl) ⟨276998, by rfl⟩ : syracuseStep 1477325 = 553997) (by norm_num)
theorem B1477349 : Blo 984595 1477349 := bbase (se 4 (by rfl) ⟨138501, by rfl⟩ : syracuseStep 1477349 = 277003) (by norm_num)
theorem B1247977 : Blo 984595 1247977 := bbase (se 2 (by rfl) ⟨467991, by rfl⟩ : syracuseStep 1247977 = 935983) (by norm_num)
theorem B1477373 : Blo 984595 1477373 := bbase (se 3 (by rfl) ⟨277007, by rfl⟩ : syracuseStep 1477373 = 554015) (by norm_num)
theorem B1477397 : Blo 984595 1477397 := bbase (se 6 (by rfl) ⟨34626, by rfl⟩ : syracuseStep 1477397 = 69253) (by norm_num)
theorem B1477421 : Blo 984595 1477421 := bbase (se 3 (by rfl) ⟨277016, by rfl⟩ : syracuseStep 1477421 = 554033) (by norm_num)
theorem B1477445 : Blo 984595 1477445 := bbase (se 4 (by rfl) ⟨138510, by rfl⟩ : syracuseStep 1477445 = 277021) (by norm_num)
theorem B1477469 : Blo 984595 1477469 := bbase (se 3 (by rfl) ⟨277025, by rfl⟩ : syracuseStep 1477469 = 554051) (by norm_num)
theorem B1477493 : Blo 984595 1477493 := bbase (se 5 (by rfl) ⟨69257, by rfl⟩ : syracuseStep 1477493 = 138515) (by norm_num)
theorem B2493301 : Blo 984595 2493301 := bbase (se 5 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 2493301 = 233747) (by norm_num)
theorem B1477517 : Blo 984595 1477517 := bbase (se 3 (by rfl) ⟨277034, by rfl⟩ : syracuseStep 1477517 = 554069) (by norm_num)
theorem B1248149 : Blo 984595 1248149 := bbase (se 6 (by rfl) ⟨29253, by rfl⟩ : syracuseStep 1248149 = 58507) (by norm_num)
theorem B1477541 : Blo 984595 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B1477565 : Blo 984595 1477565 := bbase (se 3 (by rfl) ⟨277043, by rfl⟩ : syracuseStep 1477565 = 554087) (by norm_num)
theorem B1870789 : Blo 984595 1870789 := bbase (se 4 (by rfl) ⟨175386, by rfl⟩ : syracuseStep 1870789 = 350773) (by norm_num)
theorem B1248205 : Blo 984595 1248205 := bbase (se 3 (by rfl) ⟨234038, by rfl⟩ : syracuseStep 1248205 = 468077) (by norm_num)
theorem B1477589 : Blo 984595 1477589 := bbase (se 7 (by rfl) ⟨17315, by rfl⟩ : syracuseStep 1477589 = 34631) (by norm_num)
theorem B2493413 : Blo 984595 2493413 := bbase (se 4 (by rfl) ⟨233757, by rfl⟩ : syracuseStep 2493413 = 467515) (by norm_num)
theorem B1477613 : Blo 984595 1477613 := bbase (se 3 (by rfl) ⟨277052, by rfl⟩ : syracuseStep 1477613 = 554105) (by norm_num)
theorem B1477637 : Blo 984595 1477637 := bbase (se 4 (by rfl) ⟨138528, by rfl⟩ : syracuseStep 1477637 = 277057) (by norm_num)
theorem B1477661 : Blo 984595 1477661 := bbase (se 3 (by rfl) ⟨277061, by rfl⟩ : syracuseStep 1477661 = 554123) (by norm_num)
theorem B1248301 : Blo 984595 1248301 := bbase (se 3 (by rfl) ⟨234056, by rfl⟩ : syracuseStep 1248301 = 468113) (by norm_num)
theorem B1477685 : Blo 984595 1477685 := bbase (se 5 (by rfl) ⟨69266, by rfl⟩ : syracuseStep 1477685 = 138533) (by norm_num)
theorem B1477709 : Blo 984595 1477709 := bbase (se 3 (by rfl) ⟨277070, by rfl⟩ : syracuseStep 1477709 = 554141) (by norm_num)
theorem B1870933 : Blo 984595 1870933 := bbase (se 8 (by rfl) ⟨10962, by rfl⟩ : syracuseStep 1870933 = 21925) (by norm_num)
theorem B1477733 : Blo 984595 1477733 := bbase (se 4 (by rfl) ⟨138537, by rfl⟩ : syracuseStep 1477733 = 277075) (by norm_num)
theorem B1477757 : Blo 984595 1477757 := bbase (se 3 (by rfl) ⟨277079, by rfl⟩ : syracuseStep 1477757 = 554159) (by norm_num)
theorem B1477781 : Blo 984595 1477781 := bbase (se 6 (by rfl) ⟨34635, by rfl⟩ : syracuseStep 1477781 = 69271) (by norm_num)
theorem B2493605 : Blo 984595 2493605 := bbase (se 4 (by rfl) ⟨233775, by rfl⟩ : syracuseStep 2493605 = 467551) (by norm_num)
theorem B1477805 : Blo 984595 1477805 := bbase (se 3 (by rfl) ⟨277088, by rfl⟩ : syracuseStep 1477805 = 554177) (by norm_num)
theorem B1477829 : Blo 984595 1477829 := bbase (se 4 (by rfl) ⟨138546, by rfl⟩ : syracuseStep 1477829 = 277093) (by norm_num)
theorem B2002117 : Blo 984595 2002117 := bbase (se 4 (by rfl) ⟨187698, by rfl⟩ : syracuseStep 2002117 = 375397) (by norm_num)
theorem B1182937 : Blo 984595 1182937 := bbase (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) (by norm_num)
theorem B1248473 : Blo 984595 1248473 := bbase (se 2 (by rfl) ⟨468177, by rfl⟩ : syracuseStep 1248473 = 936355) (by norm_num)
theorem B1477853 : Blo 984595 1477853 := bbase (se 3 (by rfl) ⟨277097, by rfl⟩ : syracuseStep 1477853 = 554195) (by norm_num)
theorem B1477877 : Blo 984595 1477877 := bbase (se 5 (by rfl) ⟨69275, by rfl⟩ : syracuseStep 1477877 = 138551) (by norm_num)
theorem B1871093 : Blo 984595 1871093 := bbase (se 5 (by rfl) ⟨87707, by rfl⟩ : syracuseStep 1871093 = 175415) (by norm_num)
theorem B1051913 : Blo 984595 1051913 := bbase (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) (by norm_num)
theorem B1477901 : Blo 984595 1477901 := bbase (se 3 (by rfl) ⟨277106, by rfl⟩ : syracuseStep 1477901 = 554213) (by norm_num)
theorem B1248529 : Blo 984595 1248529 := bbase (se 2 (by rfl) ⟨468198, by rfl⟩ : syracuseStep 1248529 = 936397) (by norm_num)
theorem B1477925 : Blo 984595 1477925 := bbase (se 4 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 1477925 = 277111) (by norm_num)
theorem B1477949 : Blo 984595 1477949 := bbase (se 3 (by rfl) ⟨277115, by rfl⟩ : syracuseStep 1477949 = 554231) (by norm_num)
theorem B1477973 : Blo 984595 1477973 := bbase (se 11 (by rfl) ⟨1082, by rfl⟩ : syracuseStep 1477973 = 2165) (by norm_num)
theorem B1477997 : Blo 984595 1477997 := bbase (se 3 (by rfl) ⟨277124, by rfl⟩ : syracuseStep 1477997 = 554249) (by norm_num)
theorem B1248625 : Blo 984595 1248625 := bbase (se 2 (by rfl) ⟨468234, by rfl⟩ : syracuseStep 1248625 = 936469) (by norm_num)
theorem B1478021 : Blo 984595 1478021 := bbase (se 4 (by rfl) ⟨138564, by rfl⟩ : syracuseStep 1478021 = 277129) (by norm_num)
theorem B1871237 : Blo 984595 1871237 := bbase (se 4 (by rfl) ⟨175428, by rfl⟩ : syracuseStep 1871237 = 350857) (by norm_num)
theorem B1478045 : Blo 984595 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B1478069 : Blo 984595 1478069 := bbase (se 5 (by rfl) ⟨69284, by rfl⟩ : syracuseStep 1478069 = 138569) (by norm_num)
theorem B1478093 : Blo 984595 1478093 := bbase (se 3 (by rfl) ⟨277142, by rfl⟩ : syracuseStep 1478093 = 554285) (by norm_num)
theorem B1478117 : Blo 984595 1478117 := bbase (se 4 (by rfl) ⟨138573, by rfl⟩ : syracuseStep 1478117 = 277147) (by norm_num)
theorem B7114229 : Blo 984595 7114229 := bbase (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) (by norm_num)
theorem B2493949 : Blo 984595 2493949 := bbase (se 3 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 2493949 = 935231) (by norm_num)
theorem B1478141 : Blo 984595 1478141 := bbase (se 3 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 1478141 = 554303) (by norm_num)
theorem B1478165 : Blo 984595 1478165 := bbase (se 6 (by rfl) ⟨34644, by rfl⟩ : syracuseStep 1478165 = 69289) (by norm_num)
theorem B1248797 : Blo 984595 1248797 := bbase (se 3 (by rfl) ⟨234149, by rfl⟩ : syracuseStep 1248797 = 468299) (by norm_num)
theorem B1478189 : Blo 984595 1478189 := bbase (se 3 (by rfl) ⟨277160, by rfl⟩ : syracuseStep 1478189 = 554321) (by norm_num)
theorem B1478213 : Blo 984595 1478213 := bbase (se 4 (by rfl) ⟨138582, by rfl⟩ : syracuseStep 1478213 = 277165) (by norm_num)
theorem B1248853 : Blo 984595 1248853 := bbase (se 8 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 1248853 = 14635) (by norm_num)
theorem B1478237 : Blo 984595 1478237 := bbase (se 3 (by rfl) ⟨277169, by rfl⟩ : syracuseStep 1478237 = 554339) (by norm_num)
theorem B2494061 : Blo 984595 2494061 := bbase (se 3 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 2494061 = 935273) (by norm_num)
theorem B1478261 : Blo 984595 1478261 := bbase (se 5 (by rfl) ⟨69293, by rfl⟩ : syracuseStep 1478261 = 138587) (by norm_num)
theorem B1478285 : Blo 984595 1478285 := bbase (se 3 (by rfl) ⟨277178, by rfl⟩ : syracuseStep 1478285 = 554357) (by norm_num)
theorem B2526869 : Blo 984595 2526869 := bbase (se 6 (by rfl) ⟨59223, by rfl⟩ : syracuseStep 2526869 = 118447) (by norm_num)
theorem B1478309 : Blo 984595 1478309 := bbase (se 4 (by rfl) ⟨138591, by rfl⟩ : syracuseStep 1478309 = 277183) (by norm_num)
theorem B1871525 : Blo 984595 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B1248949 : Blo 984595 1248949 := bbase (se 5 (by rfl) ⟨58544, by rfl⟩ : syracuseStep 1248949 = 117089) (by norm_num)
theorem B1478333 : Blo 984595 1478333 := bbase (se 3 (by rfl) ⟨277187, by rfl⟩ : syracuseStep 1478333 = 554375) (by norm_num)
theorem B1052357 : Blo 984595 1052357 := bbase (se 4 (by rfl) ⟨98658, by rfl⟩ : syracuseStep 1052357 = 197317) (by norm_num)
theorem B1478357 : Blo 984595 1478357 := bbase (se 7 (by rfl) ⟨17324, by rfl⟩ : syracuseStep 1478357 = 34649) (by norm_num)
theorem B1478381 : Blo 984595 1478381 := bbase (se 3 (by rfl) ⟨277196, by rfl⟩ : syracuseStep 1478381 = 554393) (by norm_num)
theorem B1478405 : Blo 984595 1478405 := bbase (se 4 (by rfl) ⟨138600, by rfl⟩ : syracuseStep 1478405 = 277201) (by norm_num)
theorem B1478429 : Blo 984595 1478429 := bbase (se 3 (by rfl) ⟨277205, by rfl⟩ : syracuseStep 1478429 = 554411) (by norm_num)
theorem B2494253 : Blo 984595 2494253 := bbase (se 3 (by rfl) ⟨467672, by rfl⟩ : syracuseStep 2494253 = 935345) (by norm_num)
theorem B2002733 : Blo 984595 2002733 := bbase (se 3 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 2002733 = 751025) (by norm_num)
theorem B1478453 : Blo 984595 1478453 := bbase (se 5 (by rfl) ⟨69302, by rfl⟩ : syracuseStep 1478453 = 138605) (by norm_num)
theorem B1871677 : Blo 984595 1871677 := bbase (se 3 (by rfl) ⟨350939, by rfl⟩ : syracuseStep 1871677 = 701879) (by norm_num)
theorem B1478477 : Blo 984595 1478477 := bbase (se 3 (by rfl) ⟨277214, by rfl⟩ : syracuseStep 1478477 = 554429) (by norm_num)
theorem B1249121 : Blo 984595 1249121 := bbase (se 2 (by rfl) ⟨468420, by rfl⟩ : syracuseStep 1249121 = 936841) (by norm_num)
theorem B1478501 : Blo 984595 1478501 := bbase (se 4 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 1478501 = 277219) (by norm_num)
theorem B1478525 : Blo 984595 1478525 := bbase (se 3 (by rfl) ⟨277223, by rfl⟩ : syracuseStep 1478525 = 554447) (by norm_num)
theorem B2527109 : Blo 984595 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1478549 : Blo 984595 1478549 := bbase (se 6 (by rfl) ⟨34653, by rfl⟩ : syracuseStep 1478549 = 69307) (by norm_num)
theorem B1249177 : Blo 984595 1249177 := bbase (se 2 (by rfl) ⟨468441, by rfl⟩ : syracuseStep 1249177 = 936883) (by norm_num)
theorem B1478573 : Blo 984595 1478573 := bbase (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) (by norm_num)
theorem B1052605 : Blo 984595 1052605 := bbase (se 3 (by rfl) ⟨197363, by rfl⟩ : syracuseStep 1052605 = 394727) (by norm_num)
theorem B1478597 : Blo 984595 1478597 := bbase (se 4 (by rfl) ⟨138618, by rfl⟩ : syracuseStep 1478597 = 277237) (by norm_num)
theorem B1478621 : Blo 984595 1478621 := bbase (se 3 (by rfl) ⟨277241, by rfl⟩ : syracuseStep 1478621 = 554483) (by norm_num)
theorem B1478645 : Blo 984595 1478645 := bbase (se 5 (by rfl) ⟨69311, by rfl⟩ : syracuseStep 1478645 = 138623) (by norm_num)
theorem B1249273 : Blo 984595 1249273 := bbase (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) (by norm_num)
theorem B1478669 : Blo 984595 1478669 := bbase (se 3 (by rfl) ⟨277250, by rfl⟩ : syracuseStep 1478669 = 554501) (by norm_num)
theorem B1478693 : Blo 984595 1478693 := bbase (se 4 (by rfl) ⟨138627, by rfl⟩ : syracuseStep 1478693 = 277255) (by norm_num)
theorem B1478717 : Blo 984595 1478717 := bbase (se 3 (by rfl) ⟨277259, by rfl⟩ : syracuseStep 1478717 = 554519) (by norm_num)
theorem B4984901 : Blo 984595 4984901 := bbase (se 4 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 4984901 = 934669) (by norm_num)
theorem B2527301 : Blo 984595 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B1183825 : Blo 984595 1183825 := bbase (se 2 (by rfl) ⟨443934, by rfl⟩ : syracuseStep 1183825 = 887869) (by norm_num)
theorem B1478741 : Blo 984595 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B1478765 : Blo 984595 1478765 := bbase (se 3 (by rfl) ⟨277268, by rfl⟩ : syracuseStep 1478765 = 554537) (by norm_num)
theorem B1871981 : Blo 984595 1871981 := bbase (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) (by norm_num)
theorem B2494597 : Blo 984595 2494597 := bbase (se 4 (by rfl) ⟨233868, by rfl⟩ : syracuseStep 2494597 = 467737) (by norm_num)
theorem B1478789 : Blo 984595 1478789 := bbase (se 4 (by rfl) ⟨138636, by rfl⟩ : syracuseStep 1478789 = 277273) (by norm_num)
theorem B1478813 : Blo 984595 1478813 := bbase (se 3 (by rfl) ⟨277277, by rfl⟩ : syracuseStep 1478813 = 554555) (by norm_num)
theorem B1249445 : Blo 984595 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B1478837 : Blo 984595 1478837 := bbase (se 5 (by rfl) ⟨69320, by rfl⟩ : syracuseStep 1478837 = 138641) (by norm_num)
theorem B1478861 : Blo 984595 1478861 := bbase (se 3 (by rfl) ⟨277286, by rfl⟩ : syracuseStep 1478861 = 554573) (by norm_num)
theorem B1249501 : Blo 984595 1249501 := bbase (se 3 (by rfl) ⟨234281, by rfl⟩ : syracuseStep 1249501 = 468563) (by norm_num)
theorem B3739877 : Blo 984595 3739877 := bbase (se 4 (by rfl) ⟨350613, by rfl⟩ : syracuseStep 3739877 = 701227) (by norm_num)
theorem B1478885 : Blo 984595 1478885 := bbase (se 4 (by rfl) ⟨138645, by rfl⟩ : syracuseStep 1478885 = 277291) (by norm_num)
theorem B2494709 : Blo 984595 2494709 := bbase (se 5 (by rfl) ⟨116939, by rfl⟩ : syracuseStep 2494709 = 233879) (by norm_num)
theorem B1478909 : Blo 984595 1478909 := bbase (se 3 (by rfl) ⟨277295, by rfl⟩ : syracuseStep 1478909 = 554591) (by norm_num)
theorem B1478933 : Blo 984595 1478933 := bbase (se 6 (by rfl) ⟨34662, by rfl⟩ : syracuseStep 1478933 = 69325) (by norm_num)
theorem B1478957 : Blo 984595 1478957 := bbase (se 3 (by rfl) ⟨277304, by rfl⟩ : syracuseStep 1478957 = 554609) (by norm_num)
theorem B1249597 : Blo 984595 1249597 := bbase (se 3 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 1249597 = 468599) (by norm_num)
theorem B1478981 : Blo 984595 1478981 := bbase (se 4 (by rfl) ⟨138654, by rfl⟩ : syracuseStep 1478981 = 277309) (by norm_num)
theorem B1479005 : Blo 984595 1479005 := bbase (se 3 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 1479005 = 554627) (by norm_num)
theorem B1053037 : Blo 984595 1053037 := bbase (se 3 (by rfl) ⟨197444, by rfl⟩ : syracuseStep 1053037 = 394889) (by norm_num)
theorem B1479029 : Blo 984595 1479029 := bbase (se 5 (by rfl) ⟨69329, by rfl⟩ : syracuseStep 1479029 = 138659) (by norm_num)
theorem B3379589 : Blo 984595 3379589 := bbase (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) (by norm_num)
theorem B1479053 : Blo 984595 1479053 := bbase (se 3 (by rfl) ⟨277322, by rfl⟩ : syracuseStep 1479053 = 554645) (by norm_num)
theorem B1479077 : Blo 984595 1479077 := bbase (se 4 (by rfl) ⟨138663, by rfl⟩ : syracuseStep 1479077 = 277327) (by norm_num)
theorem B2494901 : Blo 984595 2494901 := bbase (se 5 (by rfl) ⟨116948, by rfl⟩ : syracuseStep 2494901 = 233897) (by norm_num)
theorem B1053109 : Blo 984595 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B1479101 : Blo 984595 1479101 := bbase (se 3 (by rfl) ⟨277331, by rfl⟩ : syracuseStep 1479101 = 554663) (by norm_num)
theorem B1479125 : Blo 984595 1479125 := bbase (se 7 (by rfl) ⟨17333, by rfl⟩ : syracuseStep 1479125 = 34667) (by norm_num)
theorem B1249769 : Blo 984595 1249769 := bbase (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) (by norm_num)
theorem B1479149 : Blo 984595 1479149 := bbase (se 3 (by rfl) ⟨277340, by rfl⟩ : syracuseStep 1479149 = 554681) (by norm_num)
theorem B3740165 : Blo 984595 3740165 := bbase (se 4 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 3740165 = 701281) (by norm_num)
theorem B1479173 : Blo 984595 1479173 := bbase (se 4 (by rfl) ⟨138672, by rfl⟩ : syracuseStep 1479173 = 277345) (by norm_num)
theorem B1577485 : Blo 984595 1577485 := bbase (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) (by norm_num)
theorem B1479197 : Blo 984595 1479197 := bbase (se 3 (by rfl) ⟨277349, by rfl⟩ : syracuseStep 1479197 = 554699) (by norm_num)
theorem B1249825 : Blo 984595 1249825 := bbase (se 2 (by rfl) ⟨468684, by rfl⟩ : syracuseStep 1249825 = 937369) (by norm_num)
theorem B1479221 : Blo 984595 1479221 := bbase (se 5 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 1479221 = 138677) (by norm_num)
theorem B3379765 : Blo 984595 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B1479245 : Blo 984595 1479245 := bbase (se 3 (by rfl) ⟨277358, by rfl⟩ : syracuseStep 1479245 = 554717) (by norm_num)
theorem B1479269 : Blo 984595 1479269 := bbase (se 4 (by rfl) ⟨138681, by rfl⟩ : syracuseStep 1479269 = 277363) (by norm_num)
theorem B2527853 : Blo 984595 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B9474677 : Blo 984595 9474677 := bbase (se 5 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 9474677 = 888251) (by norm_num)
theorem B1479293 : Blo 984595 1479293 := bbase (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) (by norm_num)
theorem B1249921 : Blo 984595 1249921 := bbase (se 2 (by rfl) ⟨468720, by rfl⟩ : syracuseStep 1249921 = 937441) (by norm_num)
theorem B1479317 : Blo 984595 1479317 := bbase (se 6 (by rfl) ⟨34671, by rfl⟩ : syracuseStep 1479317 = 69343) (by norm_num)
theorem B1479341 : Blo 984595 1479341 := bbase (se 3 (by rfl) ⟨277376, by rfl⟩ : syracuseStep 1479341 = 554753) (by norm_num)
theorem B4264645 : Blo 984595 4264645 := bbase (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) (by norm_num)
theorem B1479365 : Blo 984595 1479365 := bbase (se 4 (by rfl) ⟨138690, by rfl⟩ : syracuseStep 1479365 = 277381) (by norm_num)
theorem B2527957 : Blo 984595 2527957 := bbase (se 7 (by rfl) ⟨29624, by rfl⟩ : syracuseStep 2527957 = 59249) (by norm_num)
theorem B1479389 : Blo 984595 1479389 := bbase (se 3 (by rfl) ⟨277385, by rfl⟩ : syracuseStep 1479389 = 554771) (by norm_num)
theorem B4002533 : Blo 984595 4002533 := bbase (se 4 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 4002533 = 750475) (by norm_num)
theorem B1479413 : Blo 984595 1479413 := bbase (se 5 (by rfl) ⟨69347, by rfl⟩ : syracuseStep 1479413 = 138695) (by norm_num)
theorem B2495245 : Blo 984595 2495245 := bbase (se 3 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 2495245 = 935717) (by norm_num)
theorem B1479437 : Blo 984595 1479437 := bbase (se 3 (by rfl) ⟨277394, by rfl⟩ : syracuseStep 1479437 = 554789) (by norm_num)
theorem B1479461 : Blo 984595 1479461 := bbase (se 4 (by rfl) ⟨138699, by rfl⟩ : syracuseStep 1479461 = 277399) (by norm_num)
theorem B1053481 : Blo 984595 1053481 := bbase (se 2 (by rfl) ⟨395055, by rfl⟩ : syracuseStep 1053481 = 790111) (by norm_num)
theorem B1250093 : Blo 984595 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B1479485 : Blo 984595 1479485 := bbase (se 3 (by rfl) ⟨277403, by rfl⟩ : syracuseStep 1479485 = 554807) (by norm_num)
theorem B1479509 : Blo 984595 1479509 := bbase (se 9 (by rfl) ⟨4334, by rfl⟩ : syracuseStep 1479509 = 8669) (by norm_num)
theorem B1872733 : Blo 984595 1872733 := bbase (se 3 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 1872733 = 702275) (by norm_num)
theorem B1250149 : Blo 984595 1250149 := bbase (se 4 (by rfl) ⟨117201, by rfl⟩ : syracuseStep 1250149 = 234403) (by norm_num)
theorem B1479533 : Blo 984595 1479533 := bbase (se 3 (by rfl) ⟨277412, by rfl⟩ : syracuseStep 1479533 = 554825) (by norm_num)
theorem B2495357 : Blo 984595 2495357 := bbase (se 3 (by rfl) ⟨467879, by rfl⟩ : syracuseStep 2495357 = 935759) (by norm_num)
theorem B1479557 : Blo 984595 1479557 := bbase (se 4 (by rfl) ⟨138708, by rfl⟩ : syracuseStep 1479557 = 277417) (by norm_num)
theorem B2003861 : Blo 984595 2003861 := bbase (se 6 (by rfl) ⟨46965, by rfl⟩ : syracuseStep 2003861 = 93931) (by norm_num)
theorem B1479581 : Blo 984595 1479581 := bbase (se 3 (by rfl) ⟨277421, by rfl⟩ : syracuseStep 1479581 = 554843) (by norm_num)
theorem B1479605 : Blo 984595 1479605 := bbase (se 5 (by rfl) ⟨69356, by rfl⟩ : syracuseStep 1479605 = 138713) (by norm_num)
theorem B1250245 : Blo 984595 1250245 := bbase (se 4 (by rfl) ⟨117210, by rfl⟩ : syracuseStep 1250245 = 234421) (by norm_num)
theorem B1479629 : Blo 984595 1479629 := bbase (se 3 (by rfl) ⟨277430, by rfl⟩ : syracuseStep 1479629 = 554861) (by norm_num)
theorem B1479653 : Blo 984595 1479653 := bbase (se 4 (by rfl) ⟨138717, by rfl⟩ : syracuseStep 1479653 = 277435) (by norm_num)
theorem B3085285 : Blo 984595 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B1872877 : Blo 984595 1872877 := bbase (se 3 (by rfl) ⟨351164, by rfl⟩ : syracuseStep 1872877 = 702329) (by norm_num)
theorem B1479677 : Blo 984595 1479677 := bbase (se 3 (by rfl) ⟨277439, by rfl⟩ : syracuseStep 1479677 = 554879) (by norm_num)
theorem B1479701 : Blo 984595 1479701 := bbase (se 6 (by rfl) ⟨34680, by rfl⟩ : syracuseStep 1479701 = 69361) (by norm_num)
theorem B1479725 : Blo 984595 1479725 := bbase (se 3 (by rfl) ⟨277448, by rfl⟩ : syracuseStep 1479725 = 554897) (by norm_num)
theorem B1578037 : Blo 984595 1578037 := bbase (se 5 (by rfl) ⟨73970, by rfl⟩ : syracuseStep 1578037 = 147941) (by norm_num)
theorem B2135093 : Blo 984595 2135093 := bbase (se 5 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 2135093 = 200165) (by norm_num)
theorem B2495549 : Blo 984595 2495549 := bbase (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) (by norm_num)
theorem B1479749 : Blo 984595 1479749 := bbase (se 4 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 1479749 = 277453) (by norm_num)
theorem B1479773 : Blo 984595 1479773 := bbase (se 3 (by rfl) ⟨277457, by rfl⟩ : syracuseStep 1479773 = 554915) (by norm_num)
theorem B1184873 : Blo 984595 1184873 := bbase (se 2 (by rfl) ⟨444327, by rfl⟩ : syracuseStep 1184873 = 888655) (by norm_num)
theorem B1250417 : Blo 984595 1250417 := bbase (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) (by norm_num)
theorem B1479797 : Blo 984595 1479797 := bbase (se 5 (by rfl) ⟨69365, by rfl⟩ : syracuseStep 1479797 = 138731) (by norm_num)
theorem B1479821 : Blo 984595 1479821 := bbase (se 3 (by rfl) ⟨277466, by rfl⟩ : syracuseStep 1479821 = 554933) (by norm_num)
theorem B1873037 : Blo 984595 1873037 := bbase (se 3 (by rfl) ⟨351194, by rfl⟩ : syracuseStep 1873037 = 702389) (by norm_num)
theorem B1053857 : Blo 984595 1053857 := bbase (se 2 (by rfl) ⟨395196, by rfl⟩ : syracuseStep 1053857 = 790393) (by norm_num)
theorem B1479845 : Blo 984595 1479845 := bbase (se 4 (by rfl) ⟨138735, by rfl⟩ : syracuseStep 1479845 = 277471) (by norm_num)
theorem B1250473 : Blo 984595 1250473 := bbase (se 2 (by rfl) ⟨468927, by rfl⟩ : syracuseStep 1250473 = 937855) (by norm_num)
theorem B1479869 : Blo 984595 1479869 := bbase (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) (by norm_num)
theorem B1479893 : Blo 984595 1479893 := bbase (se 7 (by rfl) ⟨17342, by rfl⟩ : syracuseStep 1479893 = 34685) (by norm_num)
theorem B1053929 : Blo 984595 1053929 := bbase (se 2 (by rfl) ⟨395223, by rfl⟩ : syracuseStep 1053929 = 790447) (by norm_num)
theorem B1479917 : Blo 984595 1479917 := bbase (se 3 (by rfl) ⟨277484, by rfl⟩ : syracuseStep 1479917 = 554969) (by norm_num)
theorem B1479941 : Blo 984595 1479941 := bbase (se 4 (by rfl) ⟨138744, by rfl⟩ : syracuseStep 1479941 = 277489) (by norm_num)
theorem B1250569 : Blo 984595 1250569 := bbase (se 2 (by rfl) ⟨468963, by rfl⟩ : syracuseStep 1250569 = 937927) (by norm_num)
theorem B1479965 : Blo 984595 1479965 := bbase (se 3 (by rfl) ⟨277493, by rfl⟩ : syracuseStep 1479965 = 554987) (by norm_num)
theorem B1873181 : Blo 984595 1873181 := bbase (se 3 (by rfl) ⟨351221, by rfl⟩ : syracuseStep 1873181 = 702443) (by norm_num)
theorem B1578293 : Blo 984595 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B1479989 : Blo 984595 1479989 := bbase (se 5 (by rfl) ⟨69374, by rfl⟩ : syracuseStep 1479989 = 138749) (by norm_num)
theorem B1480013 : Blo 984595 1480013 := bbase (se 3 (by rfl) ⟨277502, by rfl⟩ : syracuseStep 1480013 = 555005) (by norm_num)
theorem B4986197 : Blo 984595 4986197 := bbase (se 14 (by rfl) ⟨456, by rfl⟩ : syracuseStep 4986197 = 913) (by norm_num)
theorem B1480037 : Blo 984595 1480037 := bbase (se 4 (by rfl) ⟨138753, by rfl⟩ : syracuseStep 1480037 = 277507) (by norm_num)
theorem B1480061 : Blo 984595 1480061 := bbase (se 3 (by rfl) ⟨277511, by rfl⟩ : syracuseStep 1480061 = 555023) (by norm_num)
theorem B2495893 : Blo 984595 2495893 := bbase (se 6 (by rfl) ⟨58497, by rfl⟩ : syracuseStep 2495893 = 116995) (by norm_num)
theorem B1480085 : Blo 984595 1480085 := bbase (se 6 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 1480085 = 69379) (by norm_num)
theorem B1054117 : Blo 984595 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B1480109 : Blo 984595 1480109 := bbase (se 3 (by rfl) ⟨277520, by rfl⟩ : syracuseStep 1480109 = 555041) (by norm_num)
theorem B1250741 : Blo 984595 1250741 := bbase (se 5 (by rfl) ⟨58628, by rfl⟩ : syracuseStep 1250741 = 117257) (by norm_num)
theorem B1480133 : Blo 984595 1480133 := bbase (se 4 (by rfl) ⟨138762, by rfl⟩ : syracuseStep 1480133 = 277525) (by norm_num)
theorem B1185229 : Blo 984595 1185229 := bbase (se 3 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 1185229 = 444461) (by norm_num)
theorem B1480157 : Blo 984595 1480157 := bbase (se 3 (by rfl) ⟨277529, by rfl⟩ : syracuseStep 1480157 = 555059) (by norm_num)
theorem B1250797 : Blo 984595 1250797 := bbase (se 3 (by rfl) ⟨234524, by rfl⟩ : syracuseStep 1250797 = 469049) (by norm_num)
theorem B1480181 : Blo 984595 1480181 := bbase (se 5 (by rfl) ⟨69383, by rfl⟩ : syracuseStep 1480181 = 138767) (by norm_num)
theorem B2496005 : Blo 984595 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B1480205 : Blo 984595 1480205 := bbase (se 3 (by rfl) ⟨277538, by rfl⟩ : syracuseStep 1480205 = 555077) (by norm_num)
theorem B1480229 : Blo 984595 1480229 := bbase (se 4 (by rfl) ⟨138771, by rfl⟩ : syracuseStep 1480229 = 277543) (by norm_num)
theorem B1480253 : Blo 984595 1480253 := bbase (se 3 (by rfl) ⟨277547, by rfl⟩ : syracuseStep 1480253 = 555095) (by norm_num)
theorem B1873469 : Blo 984595 1873469 := bbase (se 3 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 1873469 = 702551) (by norm_num)
theorem B2102861 : Blo 984595 2102861 := bbase (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) (by norm_num)
theorem B1250893 : Blo 984595 1250893 := bbase (se 3 (by rfl) ⟨234542, by rfl⟩ : syracuseStep 1250893 = 469085) (by norm_num)
theorem B2102869 : Blo 984595 2102869 := bbase (se 8 (by rfl) ⟨12321, by rfl⟩ : syracuseStep 2102869 = 24643) (by norm_num)
theorem B1480277 : Blo 984595 1480277 := bbase (se 8 (by rfl) ⟨8673, by rfl⟩ : syracuseStep 1480277 = 17347) (by norm_num)
theorem B1054301 : Blo 984595 1054301 := bbase (se 3 (by rfl) ⟨197681, by rfl⟩ : syracuseStep 1054301 = 395363) (by norm_num)
theorem B1480301 : Blo 984595 1480301 := bbase (se 3 (by rfl) ⟨277556, by rfl⟩ : syracuseStep 1480301 = 555113) (by norm_num)
theorem B1480325 : Blo 984595 1480325 := bbase (se 4 (by rfl) ⟨138780, by rfl⟩ : syracuseStep 1480325 = 277561) (by norm_num)
theorem B1185421 : Blo 984595 1185421 := bbase (se 3 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 1185421 = 444533) (by norm_num)
theorem B1480349 : Blo 984595 1480349 := bbase (se 3 (by rfl) ⟨277565, by rfl⟩ : syracuseStep 1480349 = 555131) (by norm_num)
theorem B3741349 : Blo 984595 3741349 := bbase (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) (by norm_num)
theorem B1480373 : Blo 984595 1480373 := bbase (se 5 (by rfl) ⟨69392, by rfl⟩ : syracuseStep 1480373 = 138785) (by norm_num)
theorem B2496197 : Blo 984595 2496197 := bbase (se 4 (by rfl) ⟨234018, by rfl⟩ : syracuseStep 2496197 = 468037) (by norm_num)
theorem B1480397 : Blo 984595 1480397 := bbase (se 3 (by rfl) ⟨277574, by rfl⟩ : syracuseStep 1480397 = 555149) (by norm_num)
theorem B1873621 : Blo 984595 1873621 := bbase (se 7 (by rfl) ⟨21956, by rfl⟩ : syracuseStep 1873621 = 43913) (by norm_num)
theorem B1480421 : Blo 984595 1480421 := bbase (se 4 (by rfl) ⟨138789, by rfl⟩ : syracuseStep 1480421 = 277579) (by norm_num)
theorem B1251065 : Blo 984595 1251065 := bbase (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) (by norm_num)
theorem B1480445 : Blo 984595 1480445 := bbase (se 3 (by rfl) ⟨277583, by rfl⟩ : syracuseStep 1480445 = 555167) (by norm_num)
theorem B1480469 : Blo 984595 1480469 := bbase (se 6 (by rfl) ⟨34698, by rfl⟩ : syracuseStep 1480469 = 69397) (by norm_num)
theorem B1185565 : Blo 984595 1185565 := bbase (se 3 (by rfl) ⟨222293, by rfl⟩ : syracuseStep 1185565 = 444587) (by norm_num)
theorem B1480493 : Blo 984595 1480493 := bbase (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) (by norm_num)
theorem B1251121 : Blo 984595 1251121 := bbase (se 2 (by rfl) ⟨469170, by rfl⟩ : syracuseStep 1251121 = 938341) (by norm_num)
theorem B1480517 : Blo 984595 1480517 := bbase (se 4 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 1480517 = 277597) (by norm_num)
theorem B3610453 : Blo 984595 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B1480541 : Blo 984595 1480541 := bbase (se 3 (by rfl) ⟨277601, by rfl⟩ : syracuseStep 1480541 = 555203) (by norm_num)
theorem B7477109 : Blo 984595 7477109 := bbase (se 5 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 7477109 = 700979) (by norm_num)
theorem B1480565 : Blo 984595 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B1480589 : Blo 984595 1480589 := bbase (se 3 (by rfl) ⟨277610, by rfl⟩ : syracuseStep 1480589 = 555221) (by norm_num)
theorem B1480613 : Blo 984595 1480613 := bbase (se 4 (by rfl) ⟨138807, by rfl⟩ : syracuseStep 1480613 = 277615) (by norm_num)
theorem B1480637 : Blo 984595 1480637 := bbase (se 3 (by rfl) ⟨277619, by rfl⟩ : syracuseStep 1480637 = 555239) (by norm_num)
theorem B3741653 : Blo 984595 3741653 := bbase (se 7 (by rfl) ⟨43847, by rfl⟩ : syracuseStep 3741653 = 87695) (by norm_num)
theorem B1480661 : Blo 984595 1480661 := bbase (se 7 (by rfl) ⟨17351, by rfl⟩ : syracuseStep 1480661 = 34703) (by norm_num)
theorem B1480685 : Blo 984595 1480685 := bbase (se 3 (by rfl) ⟨277628, by rfl⟩ : syracuseStep 1480685 = 555257) (by norm_num)
theorem B1578997 : Blo 984595 1578997 := bbase (se 5 (by rfl) ⟨74015, by rfl⟩ : syracuseStep 1578997 = 148031) (by norm_num)
theorem B1873925 : Blo 984595 1873925 := bbase (se 4 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 1873925 = 351361) (by norm_num)
theorem B1480709 : Blo 984595 1480709 := bbase (se 4 (by rfl) ⟨138816, by rfl⟩ : syracuseStep 1480709 = 277633) (by norm_num)
theorem B2496541 : Blo 984595 2496541 := bbase (se 3 (by rfl) ⟨468101, by rfl⟩ : syracuseStep 2496541 = 936203) (by norm_num)
theorem B1480733 : Blo 984595 1480733 := bbase (se 3 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 1480733 = 555275) (by norm_num)
theorem B1480757 : Blo 984595 1480757 := bbase (se 5 (by rfl) ⟨69410, by rfl⟩ : syracuseStep 1480757 = 138821) (by norm_num)
theorem B1480781 : Blo 984595 1480781 := bbase (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) (by norm_num)
theorem B1480805 : Blo 984595 1480805 := bbase (se 4 (by rfl) ⟨138825, by rfl⟩ : syracuseStep 1480805 = 277651) (by norm_num)
theorem B1480829 : Blo 984595 1480829 := bbase (se 3 (by rfl) ⟨277655, by rfl⟩ : syracuseStep 1480829 = 555311) (by norm_num)
theorem B2496653 : Blo 984595 2496653 := bbase (se 3 (by rfl) ⟨468122, by rfl⟩ : syracuseStep 2496653 = 936245) (by norm_num)
theorem B1480853 : Blo 984595 1480853 := bbase (se 6 (by rfl) ⟨34707, by rfl⟩ : syracuseStep 1480853 = 69415) (by norm_num)
theorem B1480877 : Blo 984595 1480877 := bbase (se 3 (by rfl) ⟨277664, by rfl⟩ : syracuseStep 1480877 = 555329) (by norm_num)
theorem B2463925 : Blo 984595 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B1480901 : Blo 984595 1480901 := bbase (se 4 (by rfl) ⟨138834, by rfl⟩ : syracuseStep 1480901 = 277669) (by norm_num)
theorem B1480925 : Blo 984595 1480925 := bbase (se 3 (by rfl) ⟨277673, by rfl⟩ : syracuseStep 1480925 = 555347) (by norm_num)
theorem B1480949 : Blo 984595 1480949 := bbase (se 5 (by rfl) ⟨69419, by rfl⟩ : syracuseStep 1480949 = 138839) (by norm_num)
theorem B1480973 : Blo 984595 1480973 := bbase (se 3 (by rfl) ⟨277682, by rfl⟩ : syracuseStep 1480973 = 555365) (by norm_num)
theorem B1480997 : Blo 984595 1480997 := bbase (se 4 (by rfl) ⟨138843, by rfl⟩ : syracuseStep 1480997 = 277687) (by norm_num)
theorem B1481021 : Blo 984595 1481021 := bbase (se 3 (by rfl) ⟨277691, by rfl⟩ : syracuseStep 1481021 = 555383) (by norm_num)
theorem B2496845 : Blo 984595 2496845 := bbase (se 3 (by rfl) ⟨468158, by rfl⟩ : syracuseStep 2496845 = 936317) (by norm_num)
theorem B1055053 : Blo 984595 1055053 := bbase (se 3 (by rfl) ⟨197822, by rfl⟩ : syracuseStep 1055053 = 395645) (by norm_num)
theorem B1481045 : Blo 984595 1481045 := bbase (se 10 (by rfl) ⟨2169, by rfl⟩ : syracuseStep 1481045 = 4339) (by norm_num)
theorem B1481069 : Blo 984595 1481069 := bbase (se 3 (by rfl) ⟨277700, by rfl⟩ : syracuseStep 1481069 = 555401) (by norm_num)
theorem B1481093 : Blo 984595 1481093 := bbase (se 4 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 1481093 = 277705) (by norm_num)
theorem B1055125 : Blo 984595 1055125 := bbase (se 6 (by rfl) ⟨24729, by rfl⟩ : syracuseStep 1055125 = 49459) (by norm_num)
theorem B1579421 : Blo 984595 1579421 := bbase (se 3 (by rfl) ⟨296141, by rfl⟩ : syracuseStep 1579421 = 592283) (by norm_num)
theorem B1481117 : Blo 984595 1481117 := bbase (se 3 (by rfl) ⟨277709, by rfl⟩ : syracuseStep 1481117 = 555419) (by norm_num)
theorem B1481141 : Blo 984595 1481141 := bbase (se 5 (by rfl) ⟨69428, by rfl⟩ : syracuseStep 1481141 = 138857) (by norm_num)
theorem B1481165 : Blo 984595 1481165 := bbase (se 3 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 1481165 = 555437) (by norm_num)
theorem B1481189 : Blo 984595 1481189 := bbase (se 4 (by rfl) ⟨138861, by rfl⟩ : syracuseStep 1481189 = 277723) (by norm_num)
theorem B1481213 : Blo 984595 1481213 := bbase (se 3 (by rfl) ⟨277727, by rfl⟩ : syracuseStep 1481213 = 555455) (by norm_num)
theorem B1481237 : Blo 984595 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B1481261 : Blo 984595 1481261 := bbase (se 3 (by rfl) ⟨277736, by rfl⟩ : syracuseStep 1481261 = 555473) (by norm_num)
theorem B1481285 : Blo 984595 1481285 := bbase (se 4 (by rfl) ⟨138870, by rfl⟩ : syracuseStep 1481285 = 277741) (by norm_num)
theorem B1055305 : Blo 984595 1055305 := bbase (se 2 (by rfl) ⟨395739, by rfl⟩ : syracuseStep 1055305 = 791479) (by norm_num)
theorem B2398805 : Blo 984595 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B1481309 : Blo 984595 1481309 := bbase (se 3 (by rfl) ⟨277745, by rfl⟩ : syracuseStep 1481309 = 555491) (by norm_num)
theorem B4987493 : Blo 984595 4987493 := bbase (se 4 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 4987493 = 935155) (by norm_num)
theorem B1481333 : Blo 984595 1481333 := bbase (se 5 (by rfl) ⟨69437, by rfl⟩ : syracuseStep 1481333 = 138875) (by norm_num)
theorem B1481357 : Blo 984595 1481357 := bbase (se 3 (by rfl) ⟨277754, by rfl⟩ : syracuseStep 1481357 = 555509) (by norm_num)
theorem B2497189 : Blo 984595 2497189 := bbase (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) (by norm_num)
theorem B1481381 : Blo 984595 1481381 := bbase (se 4 (by rfl) ⟨138879, by rfl⟩ : syracuseStep 1481381 = 277759) (by norm_num)
theorem B2103997 : Blo 984595 2103997 := bbase (se 3 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 2103997 = 788999) (by norm_num)
theorem B1579709 : Blo 984595 1579709 := bbase (se 3 (by rfl) ⟨296195, by rfl⟩ : syracuseStep 1579709 = 592391) (by norm_num)
theorem B1481405 : Blo 984595 1481405 := bbase (se 3 (by rfl) ⟨277763, by rfl⟩ : syracuseStep 1481405 = 555527) (by norm_num)
theorem B1481429 : Blo 984595 1481429 := bbase (se 7 (by rfl) ⟨17360, by rfl⟩ : syracuseStep 1481429 = 34721) (by norm_num)
theorem B1481453 : Blo 984595 1481453 := bbase (se 3 (by rfl) ⟨277772, by rfl⟩ : syracuseStep 1481453 = 555545) (by norm_num)
theorem B1874677 : Blo 984595 1874677 := bbase (se 5 (by rfl) ⟨87875, by rfl⟩ : syracuseStep 1874677 = 175751) (by norm_num)
theorem B1481477 : Blo 984595 1481477 := bbase (se 4 (by rfl) ⟨138888, by rfl⟩ : syracuseStep 1481477 = 277777) (by norm_num)
theorem B2497301 : Blo 984595 2497301 := bbase (se 6 (by rfl) ⟨58530, by rfl⟩ : syracuseStep 2497301 = 117061) (by norm_num)
theorem B1481501 : Blo 984595 1481501 := bbase (se 3 (by rfl) ⟨277781, by rfl⟩ : syracuseStep 1481501 = 555563) (by norm_num)
theorem B5610293 : Blo 984595 5610293 := bbase (se 5 (by rfl) ⟨262982, by rfl⟩ : syracuseStep 5610293 = 525965) (by norm_num)
theorem B1481525 : Blo 984595 1481525 := bbase (se 5 (by rfl) ⟨69446, by rfl⟩ : syracuseStep 1481525 = 138893) (by norm_num)
theorem B1481549 : Blo 984595 1481549 := bbase (se 3 (by rfl) ⟨277790, by rfl⟩ : syracuseStep 1481549 = 555581) (by norm_num)
theorem B1481573 : Blo 984595 1481573 := bbase (se 4 (by rfl) ⟨138897, by rfl⟩ : syracuseStep 1481573 = 277795) (by norm_num)
theorem B1481597 : Blo 984595 1481597 := bbase (se 3 (by rfl) ⟨277799, by rfl⟩ : syracuseStep 1481597 = 555599) (by norm_num)
theorem B1874821 : Blo 984595 1874821 := bbase (se 4 (by rfl) ⟨175764, by rfl⟩ : syracuseStep 1874821 = 351529) (by norm_num)
theorem B1481621 : Blo 984595 1481621 := bbase (se 6 (by rfl) ⟨34725, by rfl⟩ : syracuseStep 1481621 = 69451) (by norm_num)
theorem B1579933 : Blo 984595 1579933 := bbase (se 3 (by rfl) ⟨296237, by rfl⟩ : syracuseStep 1579933 = 592475) (by norm_num)
theorem B1481645 : Blo 984595 1481645 := bbase (se 3 (by rfl) ⟨277808, by rfl⟩ : syracuseStep 1481645 = 555617) (by norm_num)
theorem B1481669 : Blo 984595 1481669 := bbase (se 4 (by rfl) ⟨138906, by rfl⟩ : syracuseStep 1481669 = 277813) (by norm_num)
theorem B2497493 : Blo 984595 2497493 := bbase (se 7 (by rfl) ⟨29267, by rfl⟩ : syracuseStep 2497493 = 58535) (by norm_num)
theorem B1481693 : Blo 984595 1481693 := bbase (se 3 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 1481693 = 555635) (by norm_num)
theorem B1481717 : Blo 984595 1481717 := bbase (se 5 (by rfl) ⟨69455, by rfl⟩ : syracuseStep 1481717 = 138911) (by norm_num)
theorem B1481741 : Blo 984595 1481741 := bbase (se 3 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 1481741 = 555653) (by norm_num)
theorem B8526869 : Blo 984595 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B1874981 : Blo 984595 1874981 := bbase (se 4 (by rfl) ⟨175779, by rfl⟩ : syracuseStep 1874981 = 351559) (by norm_num)
theorem B1481765 : Blo 984595 1481765 := bbase (se 4 (by rfl) ⟨138915, by rfl⟩ : syracuseStep 1481765 = 277831) (by norm_num)
theorem B2104373 : Blo 984595 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B1481789 : Blo 984595 1481789 := bbase (se 3 (by rfl) ⟨277835, by rfl⟩ : syracuseStep 1481789 = 555671) (by norm_num)
theorem B1481813 : Blo 984595 1481813 := bbase (se 8 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 1481813 = 17365) (by norm_num)
theorem B1481837 : Blo 984595 1481837 := bbase (se 3 (by rfl) ⟨277844, by rfl⟩ : syracuseStep 1481837 = 555689) (by norm_num)
theorem B1481861 : Blo 984595 1481861 := bbase (se 4 (by rfl) ⟨138924, by rfl⟩ : syracuseStep 1481861 = 277849) (by norm_num)
theorem B1481885 : Blo 984595 1481885 := bbase (se 3 (by rfl) ⟨277853, by rfl⟩ : syracuseStep 1481885 = 555707) (by norm_num)
theorem B1875125 : Blo 984595 1875125 := bbase (se 5 (by rfl) ⟨87896, by rfl⟩ : syracuseStep 1875125 = 175793) (by norm_num)
theorem B1481909 : Blo 984595 1481909 := bbase (se 5 (by rfl) ⟨69464, by rfl⟩ : syracuseStep 1481909 = 138929) (by norm_num)
theorem B2399429 : Blo 984595 2399429 := bbase (se 4 (by rfl) ⟨224946, by rfl⟩ : syracuseStep 2399429 = 449893) (by norm_num)
theorem B1481933 : Blo 984595 1481933 := bbase (se 3 (by rfl) ⟨277862, by rfl⟩ : syracuseStep 1481933 = 555725) (by norm_num)
theorem B1481957 : Blo 984595 1481957 := bbase (se 4 (by rfl) ⟨138933, by rfl⟩ : syracuseStep 1481957 = 277867) (by norm_num)
theorem B1481981 : Blo 984595 1481981 := bbase (se 3 (by rfl) ⟨277871, by rfl⟩ : syracuseStep 1481981 = 555743) (by norm_num)
theorem B1482005 : Blo 984595 1482005 := bbase (se 6 (by rfl) ⟨34734, by rfl⟩ : syracuseStep 1482005 = 69469) (by norm_num)
theorem B1187093 : Blo 984595 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B2497837 : Blo 984595 2497837 := bbase (se 3 (by rfl) ⟨468344, by rfl⟩ : syracuseStep 2497837 = 936689) (by norm_num)
theorem B1482029 : Blo 984595 1482029 := bbase (se 3 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 1482029 = 555761) (by norm_num)
theorem B1482053 : Blo 984595 1482053 := bbase (se 4 (by rfl) ⟨138942, by rfl⟩ : syracuseStep 1482053 = 277885) (by norm_num)
theorem B1482077 : Blo 984595 1482077 := bbase (se 3 (by rfl) ⟨277889, by rfl⟩ : syracuseStep 1482077 = 555779) (by norm_num)
theorem B1482101 : Blo 984595 1482101 := bbase (se 5 (by rfl) ⟨69473, by rfl⟩ : syracuseStep 1482101 = 138947) (by norm_num)
theorem B1482125 : Blo 984595 1482125 := bbase (se 3 (by rfl) ⟨277898, by rfl⟩ : syracuseStep 1482125 = 555797) (by norm_num)
theorem B2661781 : Blo 984595 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B2497949 : Blo 984595 2497949 := bbase (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) (by norm_num)
theorem B1482149 : Blo 984595 1482149 := bbase (se 4 (by rfl) ⟨138951, by rfl⟩ : syracuseStep 1482149 = 277903) (by norm_num)
theorem B1482173 : Blo 984595 1482173 := bbase (se 3 (by rfl) ⟨277907, by rfl⟩ : syracuseStep 1482173 = 555815) (by norm_num)
theorem B1875413 : Blo 984595 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B1482197 : Blo 984595 1482197 := bbase (se 7 (by rfl) ⟨17369, by rfl⟩ : syracuseStep 1482197 = 34739) (by norm_num)
theorem B1482221 : Blo 984595 1482221 := bbase (se 3 (by rfl) ⟨277916, by rfl⟩ : syracuseStep 1482221 = 555833) (by norm_num)
theorem B1482245 : Blo 984595 1482245 := bbase (se 4 (by rfl) ⟨138960, by rfl⟩ : syracuseStep 1482245 = 277921) (by norm_num)
theorem B1482269 : Blo 984595 1482269 := bbase (se 3 (by rfl) ⟨277925, by rfl⟩ : syracuseStep 1482269 = 555851) (by norm_num)
theorem B1482293 : Blo 984595 1482293 := bbase (se 5 (by rfl) ⟨69482, by rfl⟩ : syracuseStep 1482293 = 138965) (by norm_num)
theorem B1187401 : Blo 984595 1187401 := bbase (se 2 (by rfl) ⟨445275, by rfl⟩ : syracuseStep 1187401 = 890551) (by norm_num)
theorem B1482317 : Blo 984595 1482317 := bbase (se 3 (by rfl) ⟨277934, by rfl⟩ : syracuseStep 1482317 = 555869) (by norm_num)
theorem B2498141 : Blo 984595 2498141 := bbase (se 3 (by rfl) ⟨468401, by rfl⟩ : syracuseStep 2498141 = 936803) (by norm_num)
theorem B1482341 : Blo 984595 1482341 := bbase (se 4 (by rfl) ⟨138969, by rfl⟩ : syracuseStep 1482341 = 277939) (by norm_num)
theorem B1875565 : Blo 984595 1875565 := bbase (se 3 (by rfl) ⟨351668, by rfl⟩ : syracuseStep 1875565 = 703337) (by norm_num)
theorem B1482365 : Blo 984595 1482365 := bbase (se 3 (by rfl) ⟨277943, by rfl⟩ : syracuseStep 1482365 = 555887) (by norm_num)
theorem B1482389 : Blo 984595 1482389 := bbase (se 6 (by rfl) ⟨34743, by rfl⟩ : syracuseStep 1482389 = 69487) (by norm_num)
theorem B1187497 : Blo 984595 1187497 := bbase (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) (by norm_num)
theorem B1482413 : Blo 984595 1482413 := bbase (se 3 (by rfl) ⟨277952, by rfl⟩ : syracuseStep 1482413 = 555905) (by norm_num)
theorem B2530997 : Blo 984595 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1482437 : Blo 984595 1482437 := bbase (se 4 (by rfl) ⟨138978, by rfl⟩ : syracuseStep 1482437 = 277957) (by norm_num)
theorem B1482461 : Blo 984595 1482461 := bbase (se 3 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 1482461 = 555923) (by norm_num)
theorem B1482485 : Blo 984595 1482485 := bbase (se 5 (by rfl) ⟨69491, by rfl⟩ : syracuseStep 1482485 = 138983) (by norm_num)
theorem B1482509 : Blo 984595 1482509 := bbase (se 3 (by rfl) ⟨277970, by rfl⟩ : syracuseStep 1482509 = 555941) (by norm_num)
theorem B1482533 : Blo 984595 1482533 := bbase (se 4 (by rfl) ⟨138987, by rfl⟩ : syracuseStep 1482533 = 277975) (by norm_num)
theorem B1482557 : Blo 984595 1482557 := bbase (se 3 (by rfl) ⟨277979, by rfl⟩ : syracuseStep 1482557 = 555959) (by norm_num)
theorem B1482581 : Blo 984595 1482581 := bbase (se 9 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 1482581 = 8687) (by norm_num)
theorem B1482605 : Blo 984595 1482605 := bbase (se 3 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 1482605 = 555977) (by norm_num)
theorem B4988789 : Blo 984595 4988789 := bbase (se 5 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 4988789 = 467699) (by norm_num)
theorem B6004597 : Blo 984595 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B1482629 : Blo 984595 1482629 := bbase (se 4 (by rfl) ⟨138996, by rfl⟩ : syracuseStep 1482629 = 277993) (by norm_num)
theorem B1875869 : Blo 984595 1875869 := bbase (se 3 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 1875869 = 703451) (by norm_num)
theorem B1482653 : Blo 984595 1482653 := bbase (se 3 (by rfl) ⟨277997, by rfl⟩ : syracuseStep 1482653 = 555995) (by norm_num)
theorem B2498485 : Blo 984595 2498485 := bbase (se 5 (by rfl) ⟨117116, by rfl⟩ : syracuseStep 2498485 = 234233) (by norm_num)
theorem B1482677 : Blo 984595 1482677 := bbase (se 5 (by rfl) ⟨69500, by rfl⟩ : syracuseStep 1482677 = 139001) (by norm_num)
theorem B1482701 : Blo 984595 1482701 := bbase (se 3 (by rfl) ⟨278006, by rfl⟩ : syracuseStep 1482701 = 556013) (by norm_num)
theorem B5611477 : Blo 984595 5611477 := bbase (se 7 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 5611477 = 131519) (by norm_num)
theorem B1482725 : Blo 984595 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B1482749 : Blo 984595 1482749 := bbase (se 3 (by rfl) ⟨278015, by rfl⟩ : syracuseStep 1482749 = 556031) (by norm_num)
theorem B1581061 : Blo 984595 1581061 := bbase (se 4 (by rfl) ⟨148224, by rfl⟩ : syracuseStep 1581061 = 296449) (by norm_num)
theorem B3743765 : Blo 984595 3743765 := bbase (se 6 (by rfl) ⟨87744, by rfl⟩ : syracuseStep 3743765 = 175489) (by norm_num)
theorem B1482773 : Blo 984595 1482773 := bbase (se 6 (by rfl) ⟨34752, by rfl⟩ : syracuseStep 1482773 = 69505) (by norm_num)
theorem B2498597 : Blo 984595 2498597 := bbase (se 4 (by rfl) ⟨234243, by rfl⟩ : syracuseStep 2498597 = 468487) (by norm_num)
theorem B1482797 : Blo 984595 1482797 := bbase (se 3 (by rfl) ⟨278024, by rfl⟩ : syracuseStep 1482797 = 556049) (by norm_num)
theorem B1482821 : Blo 984595 1482821 := bbase (se 4 (by rfl) ⟨139014, by rfl⟩ : syracuseStep 1482821 = 278029) (by norm_num)
theorem B1482845 : Blo 984595 1482845 := bbase (se 3 (by rfl) ⟨278033, by rfl⟩ : syracuseStep 1482845 = 556067) (by norm_num)
theorem B1482869 : Blo 984595 1482869 := bbase (se 5 (by rfl) ⟨69509, by rfl⟩ : syracuseStep 1482869 = 139019) (by norm_num)
theorem B1482893 : Blo 984595 1482893 := bbase (se 3 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 1482893 = 556085) (by norm_num)
theorem B2400421 : Blo 984595 2400421 := bbase (se 4 (by rfl) ⟨225039, by rfl⟩ : syracuseStep 2400421 = 450079) (by norm_num)
theorem B2498789 : Blo 984595 2498789 := bbase (se 4 (by rfl) ⟨234261, by rfl⟩ : syracuseStep 2498789 = 468523) (by norm_num)
theorem B3744053 : Blo 984595 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B1581509 : Blo 984595 1581509 := bbase (se 4 (by rfl) ⟨148266, by rfl⟩ : syracuseStep 1581509 = 296533) (by norm_num)
theorem B2499133 : Blo 984595 2499133 := bbase (se 3 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 2499133 = 937175) (by norm_num)
theorem B2663045 : Blo 984595 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B1876621 : Blo 984595 1876621 := bbase (se 3 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 1876621 = 703733) (by norm_num)
theorem B1352341 : Blo 984595 1352341 := bbase (se 6 (by rfl) ⟨31695, by rfl⟩ : syracuseStep 1352341 = 63391) (by norm_num)
theorem B2106013 : Blo 984595 2106013 := bbase (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) (by norm_num)
theorem B2499245 : Blo 984595 2499245 := bbase (se 3 (by rfl) ⟨468608, by rfl⟩ : syracuseStep 2499245 = 937217) (by norm_num)
theorem B1876765 : Blo 984595 1876765 := bbase (se 3 (by rfl) ⟨351893, by rfl⟩ : syracuseStep 1876765 = 703787) (by norm_num)
theorem B11248469 : Blo 984595 11248469 := bbase (se 9 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 11248469 = 65909) (by norm_num)
theorem B2532197 : Blo 984595 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B2499437 : Blo 984595 2499437 := bbase (se 3 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 2499437 = 937289) (by norm_num)
theorem B2368381 : Blo 984595 2368381 := bbase (se 3 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 2368381 = 888143) (by norm_num)
theorem B4990085 : Blo 984595 4990085 := bbase (se 4 (by rfl) ⟨467820, by rfl⟩ : syracuseStep 4990085 = 935641) (by norm_num)
theorem B2499781 : Blo 984595 2499781 := bbase (se 4 (by rfl) ⟨234354, by rfl⟩ : syracuseStep 2499781 = 468709) (by norm_num)
theorem B2499893 : Blo 984595 2499893 := bbase (se 5 (by rfl) ⟨117182, by rfl⟩ : syracuseStep 2499893 = 234365) (by norm_num)
theorem B2368901 : Blo 984595 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B3155381 : Blo 984595 3155381 := bbase (se 5 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 3155381 = 295817) (by norm_num)
theorem B3745237 : Blo 984595 3745237 := bbase (se 7 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 3745237 = 87779) (by norm_num)
theorem B2368997 : Blo 984595 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B2500085 : Blo 984595 2500085 := bbase (se 5 (by rfl) ⟨117191, by rfl⟩ : syracuseStep 2500085 = 234383) (by norm_num)
theorem B2106901 : Blo 984595 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B3745541 : Blo 984595 3745541 := bbase (se 4 (by rfl) ⟨351144, by rfl⟩ : syracuseStep 3745541 = 702289) (by norm_num)
theorem B2500429 : Blo 984595 2500429 := bbase (se 3 (by rfl) ⟨468830, by rfl⟩ : syracuseStep 2500429 = 937661) (by norm_num)
theorem B1124221 : Blo 984595 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B5613461 : Blo 984595 5613461 := bbase (se 6 (by rfl) ⟨131565, by rfl⟩ : syracuseStep 5613461 = 263131) (by norm_num)
theorem B1583021 : Blo 984595 1583021 := bbase (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) (by norm_num)
theorem B2500541 : Blo 984595 2500541 := bbase (se 3 (by rfl) ⟨468851, by rfl⟩ : syracuseStep 2500541 = 937703) (by norm_num)
theorem B2107397 : Blo 984595 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B1583149 : Blo 984595 1583149 := bbase (se 3 (by rfl) ⟨296840, by rfl⟩ : syracuseStep 1583149 = 593681) (by norm_num)
theorem B4499509 : Blo 984595 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B2500733 : Blo 984595 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B1124545 : Blo 984595 1124545 := bbase (se 2 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 1124545 = 843409) (by norm_num)
theorem B1779941 : Blo 984595 1779941 := bbase (se 4 (by rfl) ⟨166869, by rfl⟩ : syracuseStep 1779941 = 333739) (by norm_num)
theorem B4991381 : Blo 984595 4991381 := bbase (se 6 (by rfl) ⟨116985, by rfl⟩ : syracuseStep 4991381 = 233971) (by norm_num)
theorem B2501077 : Blo 984595 2501077 := bbase (se 7 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 2501077 = 58619) (by norm_num)
theorem B8006197 : Blo 984595 8006197 := bbase (se 5 (by rfl) ⟨375290, by rfl⟩ : syracuseStep 8006197 = 750581) (by norm_num)
theorem B2501189 : Blo 984595 2501189 := bbase (se 4 (by rfl) ⟨234486, by rfl⟩ : syracuseStep 2501189 = 468973) (by norm_num)
theorem B3156661 : Blo 984595 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B2534093 : Blo 984595 2534093 := bbase (se 3 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 2534093 = 950285) (by norm_num)
theorem B2501381 : Blo 984595 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B2370341 : Blo 984595 2370341 := bbase (se 4 (by rfl) ⟨222219, by rfl⟩ : syracuseStep 2370341 = 444439) (by norm_num)
theorem B2108261 : Blo 984595 2108261 := bbase (se 4 (by rfl) ⟨197649, by rfl⟩ : syracuseStep 2108261 = 395299) (by norm_num)
theorem B1125289 : Blo 984595 1125289 := bbase (se 2 (by rfl) ⟨421983, by rfl⟩ : syracuseStep 1125289 = 843967) (by norm_num)
theorem B2108405 : Blo 984595 2108405 := bbase (se 5 (by rfl) ⟨98831, by rfl⟩ : syracuseStep 2108405 = 197663) (by norm_num)
theorem B2501725 : Blo 984595 2501725 := bbase (se 3 (by rfl) ⟨469073, by rfl⟩ : syracuseStep 2501725 = 938147) (by norm_num)
theorem B1125517 : Blo 984595 1125517 := bbase (se 3 (by rfl) ⟨211034, by rfl⟩ : syracuseStep 1125517 = 422069) (by norm_num)
theorem B2501837 : Blo 984595 2501837 := bbase (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) (by norm_num)
theorem B2665813 : Blo 984595 2665813 := bbase (se 11 (by rfl) ⟨1952, by rfl⟩ : syracuseStep 2665813 = 3905) (by norm_num)
theorem B2502029 : Blo 984595 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B7122325 : Blo 984595 7122325 := bbase (se 6 (by rfl) ⟨166929, by rfl⟩ : syracuseStep 7122325 = 333859) (by norm_num)
theorem B1781389 : Blo 984595 1781389 := bbase (se 3 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 1781389 = 668021) (by norm_num)
theorem B4992677 : Blo 984595 4992677 := bbase (se 4 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 4992677 = 936127) (by norm_num)
theorem B2109149 : Blo 984595 2109149 := bbase (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) (by norm_num)
theorem B2502373 : Blo 984595 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B3747653 : Blo 984595 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B4206421 : Blo 984595 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B3158021 : Blo 984595 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B5615669 : Blo 984595 5615669 := bbase (se 5 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 5615669 = 526469) (by norm_num)
theorem B3747941 : Blo 984595 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B2535533 : Blo 984595 2535533 := bbase (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) (by norm_num)
theorem B3158149 : Blo 984595 3158149 := bbase (se 4 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 3158149 = 592153) (by norm_num)
theorem B3158405 : Blo 984595 3158405 := bbase (se 4 (by rfl) ⟨296100, by rfl⟩ : syracuseStep 3158405 = 592201) (by norm_num)
theorem B2109901 : Blo 984595 2109901 := bbase (se 3 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 2109901 = 791213) (by norm_num)
theorem B2994661 : Blo 984595 2994661 := bbase (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) (by norm_num)
theorem B2666981 : Blo 984595 2666981 := bbase (se 4 (by rfl) ⟨250029, by rfl⟩ : syracuseStep 2666981 = 500059) (by norm_num)
theorem B8434165 : Blo 984595 8434165 := bbase (se 5 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 8434165 = 790703) (by norm_num)
theorem B2110045 : Blo 984595 2110045 := bbase (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) (by norm_num)
theorem B2372341 : Blo 984595 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B14234453 : Blo 984595 14234453 := bbase (se 9 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 14234453 = 83405) (by norm_num)
theorem B2372485 : Blo 984595 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B2667413 : Blo 984595 2667413 := bbase (se 6 (by rfl) ⟨62517, by rfl⟩ : syracuseStep 2667413 = 125035) (by norm_num)
theorem B4993973 : Blo 984595 4993973 := bbase (se 5 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 4993973 = 468185) (by norm_num)
theorem B2110421 : Blo 984595 2110421 := bbase (se 7 (by rfl) ⟨24731, by rfl⟩ : syracuseStep 2110421 = 49463) (by norm_num)
theorem B1520837 : Blo 984595 1520837 := bbase (se 4 (by rfl) ⟨142578, by rfl⟩ : syracuseStep 1520837 = 285157) (by norm_num)
theorem B3749125 : Blo 984595 3749125 := bbase (se 4 (by rfl) ⟨351480, by rfl⟩ : syracuseStep 3749125 = 702961) (by norm_num)
theorem B4207909 : Blo 984595 4207909 := bbase (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) (by norm_num)
theorem B4207925 : Blo 984595 4207925 := bbase (se 5 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 4207925 = 394493) (by norm_num)
theorem B2110789 : Blo 984595 2110789 := bbase (se 4 (by rfl) ⟨197886, by rfl⟩ : syracuseStep 2110789 = 395773) (by norm_num)
theorem B1422749 : Blo 984595 1422749 := bbase (se 3 (by rfl) ⟨266765, by rfl⟩ : syracuseStep 1422749 = 533531) (by norm_num)
theorem B7484885 : Blo 984595 7484885 := bbase (se 7 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 7484885 = 175427) (by norm_num)
theorem B2373101 : Blo 984595 2373101 := bbase (se 3 (by rfl) ⟨444956, by rfl⟩ : syracuseStep 2373101 = 889913) (by norm_num)
theorem B6829589 : Blo 984595 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B3323429 : Blo 984595 3323429 := bbase (se 4 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 3323429 = 623143) (by norm_num)
theorem B3749429 : Blo 984595 3749429 := bbase (se 5 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 3749429 = 351509) (by norm_num)
theorem B8763125 : Blo 984595 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B2373437 : Blo 984595 2373437 := bbase (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) (by norm_num)
theorem B2373533 : Blo 984595 2373533 := bbase (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) (by norm_num)
theorem B2701253 : Blo 984595 2701253 := bbase (se 4 (by rfl) ⟨253242, by rfl⟩ : syracuseStep 2701253 = 506485) (by norm_num)
theorem B3323861 : Blo 984595 3323861 := bbase (se 7 (by rfl) ⟨38951, by rfl⟩ : syracuseStep 3323861 = 77903) (by norm_num)
theorem B8992853 : Blo 984595 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B2373725 : Blo 984595 2373725 := bbase (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) (by norm_num)
theorem B4995269 : Blo 984595 4995269 := bbase (se 4 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 4995269 = 936613) (by norm_num)
theorem B2406725 : Blo 984595 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B1849717 : Blo 984595 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B3324293 : Blo 984595 3324293 := bbase (se 4 (by rfl) ⟨311652, by rfl⟩ : syracuseStep 3324293 = 623305) (by norm_num)
theorem B8436149 : Blo 984595 8436149 := bbase (se 5 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 8436149 = 790889) (by norm_num)
theorem B5061125 : Blo 984595 5061125 := bbase (se 4 (by rfl) ⟨474480, by rfl⟩ : syracuseStep 5061125 = 948961) (by norm_num)
theorem B3160853 : Blo 984595 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B3324725 : Blo 984595 3324725 := bbase (se 5 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 3324725 = 311693) (by norm_num)
theorem B998245 : Blo 984595 998245 := bbase (se 4 (by rfl) ⟨93585, by rfl⟩ : syracuseStep 998245 = 187171) (by norm_num)
theorem B1686509 : Blo 984595 1686509 := bbase (se 3 (by rfl) ⟨316220, by rfl⟩ : syracuseStep 1686509 = 632441) (by norm_num)
theorem B998525 : Blo 984595 998525 := bbase (se 3 (by rfl) ⟨187223, by rfl⟩ : syracuseStep 998525 = 374447) (by norm_num)
theorem B2374877 : Blo 984595 2374877 := bbase (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) (by norm_num)
theorem B3325157 : Blo 984595 3325157 := bbase (se 4 (by rfl) ⟨311733, by rfl⟩ : syracuseStep 3325157 = 623467) (by norm_num)
theorem B4504981 : Blo 984595 4504981 := bbase (se 6 (by rfl) ⟨105585, by rfl⟩ : syracuseStep 4504981 = 211171) (by norm_num)
theorem B998861 : Blo 984595 998861 := bbase (se 3 (by rfl) ⟨187286, by rfl⟩ : syracuseStep 998861 = 374573) (by norm_num)
theorem B4996565 : Blo 984595 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B4210181 : Blo 984595 4210181 := bbase (se 4 (by rfl) ⟨394704, by rfl⟩ : syracuseStep 4210181 = 789409) (by norm_num)
theorem B3751541 : Blo 984595 3751541 := bbase (se 5 (by rfl) ⟨175853, by rfl⟩ : syracuseStep 3751541 = 351707) (by norm_num)
theorem B1523333 : Blo 984595 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B3325589 : Blo 984595 3325589 := bbase (se 6 (by rfl) ⟨77943, by rfl⟩ : syracuseStep 3325589 = 155887) (by norm_num)
theorem B3751829 : Blo 984595 3751829 := bbase (se 6 (by rfl) ⟨87933, by rfl⟩ : syracuseStep 3751829 = 175867) (by norm_num)
theorem B3326021 : Blo 984595 3326021 := bbase (se 4 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 3326021 = 623629) (by norm_num)
theorem B3162197 : Blo 984595 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B1425613 : Blo 984595 1425613 := bbase (se 3 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 1425613 = 534605) (by norm_num)
theorem B999761 : Blo 984595 999761 := bbase (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) (by norm_num)
theorem B3326453 : Blo 984595 3326453 := bbase (se 5 (by rfl) ⟨155927, by rfl⟩ : syracuseStep 3326453 = 311855) (by norm_num)
theorem B4735493 : Blo 984595 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B1000069 : Blo 984595 1000069 := bbase (se 4 (by rfl) ⟨93756, by rfl⟩ : syracuseStep 1000069 = 187513) (by norm_num)
theorem B1000085 : Blo 984595 1000085 := bbase (se 6 (by rfl) ⟨23439, by rfl⟩ : syracuseStep 1000085 = 46879) (by norm_num)
theorem B1622749 : Blo 984595 1622749 := bbase (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) (by norm_num)
theorem B4997861 : Blo 984595 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B3326885 : Blo 984595 3326885 := bbase (se 4 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 3326885 = 623791) (by norm_num)
theorem B2704421 : Blo 984595 2704421 := bbase (se 4 (by rfl) ⟨253539, by rfl⟩ : syracuseStep 2704421 = 507079) (by norm_num)
theorem B3753013 : Blo 984595 3753013 := bbase (se 5 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 3753013 = 351845) (by norm_num)
theorem B2999429 : Blo 984595 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B2999477 : Blo 984595 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B3327317 : Blo 984595 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B3753317 : Blo 984595 3753317 := bbase (se 4 (by rfl) ⟨351873, by rfl⟩ : syracuseStep 3753317 = 703747) (by norm_num)
theorem B5064245 : Blo 984595 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B1689341 : Blo 984595 1689341 := bbase (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) (by norm_num)
theorem B3327749 : Blo 984595 3327749 := bbase (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) (by norm_num)
theorem B4736837 : Blo 984595 4736837 := bbase (se 4 (by rfl) ⟨444078, by rfl⟩ : syracuseStep 4736837 = 888157) (by norm_num)
theorem B1066829 : Blo 984595 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B4999157 : Blo 984595 4999157 := bbase (se 5 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 4999157 = 468671) (by norm_num)
theorem B1689589 : Blo 984595 1689589 := bbase (se 5 (by rfl) ⟨79199, by rfl⟩ : syracuseStep 1689589 = 158399) (by norm_num)
theorem B3164197 : Blo 984595 3164197 := bbase (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) (by norm_num)
theorem B3328181 : Blo 984595 3328181 := bbase (se 5 (by rfl) ⟨156008, by rfl⟩ : syracuseStep 3328181 = 312017) (by norm_num)
theorem B2804053 : Blo 984595 2804053 := bbase (se 10 (by rfl) ⟨4107, by rfl⟩ : syracuseStep 2804053 = 8215) (by norm_num)
theorem B1001813 : Blo 984595 1001813 := bbase (se 10 (by rfl) ⟨1467, by rfl⟩ : syracuseStep 1001813 = 2935) (by norm_num)
theorem B2247053 : Blo 984595 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B2804213 : Blo 984595 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B8538709 : Blo 984595 8538709 := bbase (se 8 (by rfl) ⟨50031, by rfl⟩ : syracuseStep 8538709 = 100063) (by norm_num)
theorem B3328613 : Blo 984595 3328613 := bbase (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) (by norm_num)
theorem B1264297 : Blo 984595 1264297 := bbase (se 2 (by rfl) ⟨474111, by rfl⟩ : syracuseStep 1264297 = 948223) (by norm_num)
theorem B2804453 : Blo 984595 2804453 := bbase (se 4 (by rfl) ⟨262917, by rfl⟩ : syracuseStep 2804453 = 525835) (by norm_num)
theorem B2804645 : Blo 984595 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B3329045 : Blo 984595 3329045 := bbase (se 6 (by rfl) ⟨78024, by rfl⟩ : syracuseStep 3329045 = 156049) (by norm_num)
theorem B1690669 : Blo 984595 1690669 := bbase (se 3 (by rfl) ⟨317000, by rfl⟩ : syracuseStep 1690669 = 634001) (by norm_num)
theorem B7588981 : Blo 984595 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B2247821 : Blo 984595 2247821 := bbase (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) (by norm_num)
theorem B19188949 : Blo 984595 19188949 := bbase (se 7 (by rfl) ⟨224870, by rfl⟩ : syracuseStep 19188949 = 449741) (by norm_num)
theorem B5000453 : Blo 984595 5000453 := bbase (se 4 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 5000453 = 937585) (by norm_num)
theorem B2248069 : Blo 984595 2248069 := bbase (se 4 (by rfl) ⟨210756, by rfl⟩ : syracuseStep 2248069 = 421513) (by norm_num)
theorem B2215349 : Blo 984595 2215349 := bbase (se 5 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 2215349 = 207689) (by norm_num)
theorem B3329477 : Blo 984595 3329477 := bbase (se 4 (by rfl) ⟨312138, by rfl⟩ : syracuseStep 3329477 = 624277) (by norm_num)
theorem B4214213 : Blo 984595 4214213 := bbase (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) (by norm_num)
theorem B2215421 : Blo 984595 2215421 := bbase (se 3 (by rfl) ⟨415391, by rfl⟩ : syracuseStep 2215421 = 830783) (by norm_num)
theorem B2215493 : Blo 984595 2215493 := bbase (se 4 (by rfl) ⟨207702, by rfl⟩ : syracuseStep 2215493 = 415405) (by norm_num)
theorem B2215565 : Blo 984595 2215565 := bbase (se 3 (by rfl) ⟨415418, by rfl⟩ : syracuseStep 2215565 = 830837) (by norm_num)
theorem B2215637 : Blo 984595 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B4738837 : Blo 984595 4738837 := bbase (se 6 (by rfl) ⟨111066, by rfl⟩ : syracuseStep 4738837 = 222133) (by norm_num)
theorem B2215709 : Blo 984595 2215709 := bbase (se 3 (by rfl) ⟨415445, by rfl⟩ : syracuseStep 2215709 = 830891) (by norm_num)
theorem B2215781 : Blo 984595 2215781 := bbase (se 4 (by rfl) ⟨207729, by rfl⟩ : syracuseStep 2215781 = 415459) (by norm_num)
theorem B3329909 : Blo 984595 3329909 := bbase (se 5 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 3329909 = 312179) (by norm_num)
theorem B2805637 : Blo 984595 2805637 := bbase (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) (by norm_num)
theorem B2215853 : Blo 984595 2215853 := bbase (se 3 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 2215853 = 830945) (by norm_num)
theorem B2215925 : Blo 984595 2215925 := bbase (se 5 (by rfl) ⟨103871, by rfl⟩ : syracuseStep 2215925 = 207743) (by norm_num)
theorem B2215997 : Blo 984595 2215997 := bbase (se 3 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 2215997 = 830999) (by norm_num)
theorem B2216069 : Blo 984595 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B2216141 : Blo 984595 2216141 := bbase (se 3 (by rfl) ⟨415526, by rfl⟩ : syracuseStep 2216141 = 831053) (by norm_num)
theorem B2216213 : Blo 984595 2216213 := bbase (se 6 (by rfl) ⟨51942, by rfl⟩ : syracuseStep 2216213 = 103885) (by norm_num)
theorem B3330341 : Blo 984595 3330341 := bbase (se 4 (by rfl) ⟨312219, by rfl⟩ : syracuseStep 3330341 = 624439) (by norm_num)
theorem B2216285 : Blo 984595 2216285 := bbase (se 3 (by rfl) ⟨415553, by rfl⟩ : syracuseStep 2216285 = 831107) (by norm_num)
theorem B3002741 : Blo 984595 3002741 := bbase (se 5 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 3002741 = 281507) (by norm_num)
theorem B2216357 : Blo 984595 2216357 := bbase (se 4 (by rfl) ⟨207783, by rfl⟩ : syracuseStep 2216357 = 415567) (by norm_num)
theorem B1331653 : Blo 984595 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B2216429 : Blo 984595 2216429 := bbase (se 3 (by rfl) ⟨415580, by rfl⟩ : syracuseStep 2216429 = 831161) (by norm_num)
theorem B5001749 : Blo 984595 5001749 := bbase (se 6 (by rfl) ⟨117228, by rfl⟩ : syracuseStep 5001749 = 234457) (by norm_num)
theorem B2216501 : Blo 984595 2216501 := bbase (se 5 (by rfl) ⟨103898, by rfl⟩ : syracuseStep 2216501 = 207797) (by norm_num)
theorem B2216573 : Blo 984595 2216573 := bbase (se 3 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 2216573 = 831215) (by norm_num)
theorem B2249381 : Blo 984595 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B2216645 : Blo 984595 2216645 := bbase (se 4 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 2216645 = 415621) (by norm_num)
theorem B3330773 : Blo 984595 3330773 := bbase (se 7 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 3330773 = 78065) (by norm_num)
theorem B2216717 : Blo 984595 2216717 := bbase (se 3 (by rfl) ⟨415634, by rfl⟩ : syracuseStep 2216717 = 831269) (by norm_num)
theorem B1200961 : Blo 984595 1200961 := bbase (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) (by norm_num)
theorem B2216789 : Blo 984595 2216789 := bbase (se 9 (by rfl) ⟨6494, by rfl⟩ : syracuseStep 2216789 = 12989) (by norm_num)
theorem B2216861 : Blo 984595 2216861 := bbase (se 3 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 2216861 = 831323) (by norm_num)
theorem B2806741 : Blo 984595 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B2216933 : Blo 984595 2216933 := bbase (se 4 (by rfl) ⟨207837, by rfl⟩ : syracuseStep 2216933 = 415675) (by norm_num)
theorem B2217005 : Blo 984595 2217005 := bbase (se 3 (by rfl) ⟨415688, by rfl⟩ : syracuseStep 2217005 = 831377) (by norm_num)
theorem B7492661 : Blo 984595 7492661 := bbase (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) (by norm_num)
theorem B2217077 : Blo 984595 2217077 := bbase (se 5 (by rfl) ⟨103925, by rfl⟩ : syracuseStep 2217077 = 207851) (by norm_num)
theorem B2249845 : Blo 984595 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B3331205 : Blo 984595 3331205 := bbase (se 4 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 3331205 = 624601) (by norm_num)
theorem B4215989 : Blo 984595 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B2217149 : Blo 984595 2217149 := bbase (se 3 (by rfl) ⟨415715, by rfl⟩ : syracuseStep 2217149 = 831431) (by norm_num)
theorem B2217221 : Blo 984595 2217221 := bbase (se 4 (by rfl) ⟨207864, by rfl⟩ : syracuseStep 2217221 = 415729) (by norm_num)
theorem B2217293 : Blo 984595 2217293 := bbase (se 3 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 2217293 = 831485) (by norm_num)
theorem B6313301 : Blo 984595 6313301 := bbase (se 16 (by rfl) ⟨144, by rfl⟩ : syracuseStep 6313301 = 289) (by norm_num)
theorem B2217365 : Blo 984595 2217365 := bbase (se 6 (by rfl) ⟨51969, by rfl⟩ : syracuseStep 2217365 = 103939) (by norm_num)
theorem B38426069 : Blo 984595 38426069 := bbase (se 7 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 38426069 = 900611) (by norm_num)
theorem B2217437 : Blo 984595 2217437 := bbase (se 3 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 2217437 = 831539) (by norm_num)
theorem B2217509 : Blo 984595 2217509 := bbase (se 4 (by rfl) ⟨207891, by rfl⟩ : syracuseStep 2217509 = 415783) (by norm_num)
theorem B3331637 : Blo 984595 3331637 := bbase (se 5 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 3331637 = 312341) (by norm_num)
theorem B2217581 : Blo 984595 2217581 := bbase (se 3 (by rfl) ⟨415796, by rfl⟩ : syracuseStep 2217581 = 831593) (by norm_num)
theorem B2217653 : Blo 984595 2217653 := bbase (se 5 (by rfl) ⟨103952, by rfl⟩ : syracuseStep 2217653 = 207905) (by norm_num)
theorem B5625557 : Blo 984595 5625557 := bbase (se 7 (by rfl) ⟨65924, by rfl⟩ : syracuseStep 5625557 = 131849) (by norm_num)
theorem B2217725 : Blo 984595 2217725 := bbase (se 3 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 2217725 = 831647) (by norm_num)
theorem B5003045 : Blo 984595 5003045 := bbase (se 4 (by rfl) ⟨469035, by rfl⟩ : syracuseStep 5003045 = 938071) (by norm_num)
theorem B1333037 : Blo 984595 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B2217797 : Blo 984595 2217797 := bbase (se 4 (by rfl) ⟨207918, by rfl⟩ : syracuseStep 2217797 = 415837) (by norm_num)
theorem B2217869 : Blo 984595 2217869 := bbase (se 3 (by rfl) ⟨415850, by rfl⟩ : syracuseStep 2217869 = 831701) (by norm_num)
theorem B2217941 : Blo 984595 2217941 := bbase (se 7 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 2217941 = 51983) (by norm_num)
theorem B3332069 : Blo 984595 3332069 := bbase (se 4 (by rfl) ⟨312381, by rfl⟩ : syracuseStep 3332069 = 624763) (by norm_num)
theorem B2218013 : Blo 984595 2218013 := bbase (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) (by norm_num)
theorem B3561509 : Blo 984595 3561509 := bbase (se 4 (by rfl) ⟨333891, by rfl⟩ : syracuseStep 3561509 = 667783) (by norm_num)
theorem B2218085 : Blo 984595 2218085 := bbase (se 4 (by rfl) ⟨207945, by rfl⟩ : syracuseStep 2218085 = 415891) (by norm_num)
theorem B4216981 : Blo 984595 4216981 := bbase (se 6 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 4216981 = 197671) (by norm_num)
theorem B2218157 : Blo 984595 2218157 := bbase (se 3 (by rfl) ⟨415904, by rfl⟩ : syracuseStep 2218157 = 831809) (by norm_num)
theorem B2218229 : Blo 984595 2218229 := bbase (se 5 (by rfl) ⟨103979, by rfl⟩ : syracuseStep 2218229 = 207959) (by norm_num)
theorem B2218301 : Blo 984595 2218301 := bbase (se 3 (by rfl) ⟨415931, by rfl⟩ : syracuseStep 2218301 = 831863) (by norm_num)
theorem B1562941 : Blo 984595 1562941 := bbase (se 3 (by rfl) ⟨293051, by rfl⟩ : syracuseStep 1562941 = 586103) (by norm_num)
theorem B2218373 : Blo 984595 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B3332501 : Blo 984595 3332501 := bbase (se 6 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 3332501 = 156211) (by norm_num)
theorem B2808245 : Blo 984595 2808245 := bbase (se 5 (by rfl) ⟨131636, by rfl⟩ : syracuseStep 2808245 = 263273) (by norm_num)
theorem B2218445 : Blo 984595 2218445 := bbase (se 3 (by rfl) ⟨415958, by rfl⟩ : syracuseStep 2218445 = 831917) (by norm_num)
theorem B2218517 : Blo 984595 2218517 := bbase (se 6 (by rfl) ⟨51996, by rfl⟩ : syracuseStep 2218517 = 103993) (by norm_num)
theorem B1333837 : Blo 984595 1333837 := bbase (se 3 (by rfl) ⟨250094, by rfl⟩ : syracuseStep 1333837 = 500189) (by norm_num)
theorem B2218589 : Blo 984595 2218589 := bbase (se 3 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 2218589 = 831971) (by norm_num)
theorem B1661573 : Blo 984595 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B2218661 : Blo 984595 2218661 := bbase (se 4 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 2218661 = 415999) (by norm_num)
theorem B2218733 : Blo 984595 2218733 := bbase (se 3 (by rfl) ⟨416012, by rfl⟩ : syracuseStep 2218733 = 832025) (by norm_num)
theorem B1661701 : Blo 984595 1661701 := bbase (se 4 (by rfl) ⟨155784, by rfl⟩ : syracuseStep 1661701 = 311569) (by norm_num)
theorem B2218805 : Blo 984595 2218805 := bbase (se 5 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 2218805 = 208013) (by norm_num)
theorem B3332933 : Blo 984595 3332933 := bbase (se 4 (by rfl) ⟨312462, by rfl⟩ : syracuseStep 3332933 = 624925) (by norm_num)
theorem B1203017 : Blo 984595 1203017 := bbase (se 2 (by rfl) ⟨451131, by rfl⟩ : syracuseStep 1203017 = 902263) (by norm_num)
theorem B1661789 : Blo 984595 1661789 := bbase (se 3 (by rfl) ⟨311585, by rfl⟩ : syracuseStep 1661789 = 623171) (by norm_num)
theorem B2218877 : Blo 984595 2218877 := bbase (se 3 (by rfl) ⟨416039, by rfl⟩ : syracuseStep 2218877 = 832079) (by norm_num)
theorem B2218949 : Blo 984595 2218949 := bbase (se 4 (by rfl) ⟨208026, by rfl⟩ : syracuseStep 2218949 = 416053) (by norm_num)
theorem B1661917 : Blo 984595 1661917 := bbase (se 3 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 1661917 = 623219) (by norm_num)
theorem B1334237 : Blo 984595 1334237 := bbase (se 3 (by rfl) ⟨250169, by rfl⟩ : syracuseStep 1334237 = 500339) (by norm_num)
theorem B2219021 : Blo 984595 2219021 := bbase (se 3 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 2219021 = 832133) (by norm_num)
theorem B1498157 : Blo 984595 1498157 := bbase (se 3 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 1498157 = 561809) (by norm_num)
theorem B1662005 : Blo 984595 1662005 := bbase (se 5 (by rfl) ⟨77906, by rfl⟩ : syracuseStep 1662005 = 155813) (by norm_num)
theorem B5004341 : Blo 984595 5004341 := bbase (se 5 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 5004341 = 469157) (by norm_num)
theorem B2219093 : Blo 984595 2219093 := bbase (se 8 (by rfl) ⟨13002, by rfl⟩ : syracuseStep 2219093 = 26005) (by norm_num)
theorem B2219165 : Blo 984595 2219165 := bbase (se 3 (by rfl) ⟨416093, by rfl⟩ : syracuseStep 2219165 = 832187) (by norm_num)
theorem B1662133 : Blo 984595 1662133 := bbase (se 5 (by rfl) ⟨77912, by rfl⟩ : syracuseStep 1662133 = 155825) (by norm_num)
theorem B1334485 : Blo 984595 1334485 := bbase (se 7 (by rfl) ⟨15638, by rfl⟩ : syracuseStep 1334485 = 31277) (by norm_num)
theorem B2219237 : Blo 984595 2219237 := bbase (se 4 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 2219237 = 416107) (by norm_num)
theorem B3333365 : Blo 984595 3333365 := bbase (se 5 (by rfl) ⟨156251, by rfl⟩ : syracuseStep 3333365 = 312503) (by norm_num)
theorem B1662221 : Blo 984595 1662221 := bbase (se 3 (by rfl) ⟨311666, by rfl⟩ : syracuseStep 1662221 = 623333) (by norm_num)
theorem B2219309 : Blo 984595 2219309 := bbase (se 3 (by rfl) ⟨416120, by rfl⟩ : syracuseStep 2219309 = 832241) (by norm_num)
theorem B2219381 : Blo 984595 2219381 := bbase (se 5 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 2219381 = 208067) (by norm_num)
theorem B1662349 : Blo 984595 1662349 := bbase (se 3 (by rfl) ⟨311690, by rfl⟩ : syracuseStep 1662349 = 623381) (by norm_num)
theorem B1334701 : Blo 984595 1334701 := bbase (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) (by norm_num)
theorem B2219453 : Blo 984595 2219453 := bbase (se 3 (by rfl) ⟨416147, by rfl⟩ : syracuseStep 2219453 = 832295) (by norm_num)
theorem B9493973 : Blo 984595 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B1662437 : Blo 984595 1662437 := bbase (se 4 (by rfl) ⟨155853, by rfl⟩ : syracuseStep 1662437 = 311707) (by norm_num)
theorem B1924597 : Blo 984595 1924597 := bbase (se 5 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 1924597 = 180431) (by norm_num)
theorem B2219525 : Blo 984595 2219525 := bbase (se 4 (by rfl) ⟨208080, by rfl⟩ : syracuseStep 2219525 = 416161) (by norm_num)
theorem B2219597 : Blo 984595 2219597 := bbase (se 3 (by rfl) ⟨416174, by rfl⟩ : syracuseStep 2219597 = 832349) (by norm_num)
theorem B1662565 : Blo 984595 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B2219669 : Blo 984595 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B3333797 : Blo 984595 3333797 := bbase (se 4 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 3333797 = 625087) (by norm_num)
theorem B1662653 : Blo 984595 1662653 := bbase (se 3 (by rfl) ⟨311747, by rfl⟩ : syracuseStep 1662653 = 623495) (by norm_num)
theorem B2219741 : Blo 984595 2219741 := bbase (se 3 (by rfl) ⟨416201, by rfl⟩ : syracuseStep 2219741 = 832403) (by norm_num)
theorem B2219813 : Blo 984595 2219813 := bbase (se 4 (by rfl) ⟨208107, by rfl⟩ : syracuseStep 2219813 = 416215) (by norm_num)
theorem B1662781 : Blo 984595 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B2219885 : Blo 984595 2219885 := bbase (se 3 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 2219885 = 832457) (by norm_num)
theorem B1662869 : Blo 984595 1662869 := bbase (se 6 (by rfl) ⟨38973, by rfl⟩ : syracuseStep 1662869 = 77947) (by norm_num)
theorem B2219957 : Blo 984595 2219957 := bbase (se 5 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 2219957 = 208121) (by norm_num)
theorem B2809829 : Blo 984595 2809829 := bbase (se 4 (by rfl) ⟨263421, by rfl⟩ : syracuseStep 2809829 = 526843) (by norm_num)
theorem B2220029 : Blo 984595 2220029 := bbase (se 3 (by rfl) ⟨416255, by rfl⟩ : syracuseStep 2220029 = 832511) (by norm_num)
theorem B1662997 : Blo 984595 1662997 := bbase (se 6 (by rfl) ⟨38976, by rfl⟩ : syracuseStep 1662997 = 77953) (by norm_num)
theorem B2220101 : Blo 984595 2220101 := bbase (se 4 (by rfl) ⟨208134, by rfl⟩ : syracuseStep 2220101 = 416269) (by norm_num)
theorem B3334229 : Blo 984595 3334229 := bbase (se 8 (by rfl) ⟨19536, by rfl⟩ : syracuseStep 3334229 = 39073) (by norm_num)
theorem B2252893 : Blo 984595 2252893 := bbase (se 3 (by rfl) ⟨422417, by rfl⟩ : syracuseStep 2252893 = 844835) (by norm_num)
theorem B1663085 : Blo 984595 1663085 := bbase (se 3 (by rfl) ⟨311828, by rfl⟩ : syracuseStep 1663085 = 623657) (by norm_num)
theorem B2220173 : Blo 984595 2220173 := bbase (se 3 (by rfl) ⟨416282, by rfl⟩ : syracuseStep 2220173 = 832565) (by norm_num)
theorem B2220245 : Blo 984595 2220245 := bbase (se 7 (by rfl) ⟨26018, by rfl⟩ : syracuseStep 2220245 = 52037) (by norm_num)
theorem B1663213 : Blo 984595 1663213 := bbase (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) (by norm_num)
theorem B1564949 : Blo 984595 1564949 := bbase (se 6 (by rfl) ⟨36678, by rfl⟩ : syracuseStep 1564949 = 73357) (by norm_num)
theorem B2220317 : Blo 984595 2220317 := bbase (se 3 (by rfl) ⟨416309, by rfl⟩ : syracuseStep 2220317 = 832619) (by norm_num)
theorem B1663301 : Blo 984595 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B2220389 : Blo 984595 2220389 := bbase (se 4 (by rfl) ⟨208161, by rfl⟩ : syracuseStep 2220389 = 416323) (by norm_num)
theorem B2220461 : Blo 984595 2220461 := bbase (se 3 (by rfl) ⟨416336, by rfl⟩ : syracuseStep 2220461 = 832673) (by norm_num)
theorem B1663429 : Blo 984595 1663429 := bbase (se 4 (by rfl) ⟨155946, by rfl⟩ : syracuseStep 1663429 = 311893) (by norm_num)
theorem B6316501 : Blo 984595 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B2220533 : Blo 984595 2220533 := bbase (se 5 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 2220533 = 208175) (by norm_num)
theorem B5071349 : Blo 984595 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B3334661 : Blo 984595 3334661 := bbase (se 4 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 3334661 = 625249) (by norm_num)
theorem B1663517 : Blo 984595 1663517 := bbase (se 3 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 1663517 = 623819) (by norm_num)
theorem B2253349 : Blo 984595 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B2220605 : Blo 984595 2220605 := bbase (se 3 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 2220605 = 832727) (by norm_num)
theorem B2810501 : Blo 984595 2810501 := bbase (se 4 (by rfl) ⟨263484, by rfl⟩ : syracuseStep 2810501 = 526969) (by norm_num)
theorem B2220677 : Blo 984595 2220677 := bbase (se 4 (by rfl) ⟨208188, by rfl⟩ : syracuseStep 2220677 = 416377) (by norm_num)
theorem B1663645 : Blo 984595 1663645 := bbase (se 3 (by rfl) ⟨311933, by rfl⟩ : syracuseStep 1663645 = 623867) (by norm_num)
theorem B1499813 : Blo 984595 1499813 := bbase (se 4 (by rfl) ⟨140607, by rfl⟩ : syracuseStep 1499813 = 281215) (by norm_num)
theorem B2220749 : Blo 984595 2220749 := bbase (se 3 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 2220749 = 832781) (by norm_num)
theorem B1663733 : Blo 984595 1663733 := bbase (se 5 (by rfl) ⟨77987, by rfl⟩ : syracuseStep 1663733 = 155975) (by norm_num)
theorem B2220821 : Blo 984595 2220821 := bbase (se 6 (by rfl) ⟨52050, by rfl⟩ : syracuseStep 2220821 = 104101) (by norm_num)
theorem B2220893 : Blo 984595 2220893 := bbase (se 3 (by rfl) ⟨416417, by rfl⟩ : syracuseStep 2220893 = 832835) (by norm_num)
theorem B1663861 : Blo 984595 1663861 := bbase (se 5 (by rfl) ⟨77993, by rfl⟩ : syracuseStep 1663861 = 155987) (by norm_num)
theorem B2220965 : Blo 984595 2220965 := bbase (se 4 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 2220965 = 416431) (by norm_num)
theorem B3335093 : Blo 984595 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B1663949 : Blo 984595 1663949 := bbase (se 3 (by rfl) ⟨311990, by rfl⟩ : syracuseStep 1663949 = 623981) (by norm_num)
theorem B2221037 : Blo 984595 2221037 := bbase (se 3 (by rfl) ⟨416444, by rfl⟩ : syracuseStep 2221037 = 832889) (by norm_num)
theorem B2810933 : Blo 984595 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B2221109 : Blo 984595 2221109 := bbase (se 5 (by rfl) ⟨104114, by rfl⟩ : syracuseStep 2221109 = 208229) (by norm_num)
theorem B1664077 : Blo 984595 1664077 := bbase (se 3 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 1664077 = 624029) (by norm_num)
theorem B2221181 : Blo 984595 2221181 := bbase (se 3 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 2221181 = 832943) (by norm_num)
theorem B1664165 : Blo 984595 1664165 := bbase (se 4 (by rfl) ⟨156015, by rfl⟩ : syracuseStep 1664165 = 312031) (by norm_num)
theorem B2221253 : Blo 984595 2221253 := bbase (se 4 (by rfl) ⟨208242, by rfl⟩ : syracuseStep 2221253 = 416485) (by norm_num)
theorem B2254061 : Blo 984595 2254061 := bbase (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) (by norm_num)
theorem B2221325 : Blo 984595 2221325 := bbase (se 3 (by rfl) ⟨416498, by rfl⟩ : syracuseStep 2221325 = 832997) (by norm_num)
theorem B1664293 : Blo 984595 1664293 := bbase (se 4 (by rfl) ⟨156027, by rfl⟩ : syracuseStep 1664293 = 312055) (by norm_num)
theorem B1500493 : Blo 984595 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B2221397 : Blo 984595 2221397 := bbase (se 12 (by rfl) ⟨813, by rfl⟩ : syracuseStep 2221397 = 1627) (by norm_num)
theorem B3335525 : Blo 984595 3335525 := bbase (se 4 (by rfl) ⟨312705, by rfl⟩ : syracuseStep 3335525 = 625411) (by norm_num)
theorem B1664381 : Blo 984595 1664381 := bbase (se 3 (by rfl) ⟨312071, by rfl⟩ : syracuseStep 1664381 = 624143) (by norm_num)
theorem B2221469 : Blo 984595 2221469 := bbase (se 3 (by rfl) ⟨416525, by rfl⟩ : syracuseStep 2221469 = 833051) (by norm_num)
theorem B1402277 : Blo 984595 1402277 := bbase (se 4 (by rfl) ⟨131463, by rfl⟩ : syracuseStep 1402277 = 262927) (by norm_num)
theorem B2221541 : Blo 984595 2221541 := bbase (se 4 (by rfl) ⟨208269, by rfl⟩ : syracuseStep 2221541 = 416539) (by norm_num)
theorem B1664509 : Blo 984595 1664509 := bbase (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) (by norm_num)
theorem B2221613 : Blo 984595 2221613 := bbase (se 3 (by rfl) ⟨416552, by rfl⟩ : syracuseStep 2221613 = 833105) (by norm_num)
theorem B4744757 : Blo 984595 4744757 := bbase (se 5 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 4744757 = 444821) (by norm_num)
theorem B1664597 : Blo 984595 1664597 := bbase (se 8 (by rfl) ⟨9753, by rfl⟩ : syracuseStep 1664597 = 19507) (by norm_num)
theorem B2254445 : Blo 984595 2254445 := bbase (se 3 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 2254445 = 845417) (by norm_num)
theorem B2221685 : Blo 984595 2221685 := bbase (se 5 (by rfl) ⟨104141, by rfl⟩ : syracuseStep 2221685 = 208283) (by norm_num)
theorem B1926805 : Blo 984595 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B2221757 : Blo 984595 2221757 := bbase (se 3 (by rfl) ⟨416579, by rfl⟩ : syracuseStep 2221757 = 833159) (by norm_num)
theorem B1664725 : Blo 984595 1664725 := bbase (se 7 (by rfl) ⟨19508, by rfl⟩ : syracuseStep 1664725 = 39017) (by norm_num)
theorem B1042157 : Blo 984595 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B1107697 : Blo 984595 1107697 := bbase (se 2 (by rfl) ⟨415386, by rfl⟩ : syracuseStep 1107697 = 830773) (by norm_num)
theorem B2221829 : Blo 984595 2221829 := bbase (se 4 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 2221829 = 416593) (by norm_num)
theorem B1107733 : Blo 984595 1107733 := bbase (se 6 (by rfl) ⟨25962, by rfl⟩ : syracuseStep 1107733 = 51925) (by norm_num)
theorem B3335957 : Blo 984595 3335957 := bbase (se 6 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 3335957 = 156373) (by norm_num)
theorem B2811685 : Blo 984595 2811685 := bbase (se 4 (by rfl) ⟨263595, by rfl⟩ : syracuseStep 2811685 = 527191) (by norm_num)
theorem B1664813 : Blo 984595 1664813 := bbase (se 3 (by rfl) ⟨312152, by rfl⟩ : syracuseStep 1664813 = 624305) (by norm_num)
theorem B8415029 : Blo 984595 8415029 := bbase (se 5 (by rfl) ⟨394454, by rfl⟩ : syracuseStep 8415029 = 788909) (by norm_num)
theorem B1107769 : Blo 984595 1107769 := bbase (se 2 (by rfl) ⟨415413, by rfl⟩ : syracuseStep 1107769 = 830827) (by norm_num)
theorem B2221901 : Blo 984595 2221901 := bbase (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) (by norm_num)
theorem B1107805 : Blo 984595 1107805 := bbase (se 3 (by rfl) ⟨207713, by rfl⟩ : syracuseStep 1107805 = 415427) (by norm_num)
theorem B1107841 : Blo 984595 1107841 := bbase (se 2 (by rfl) ⟨415440, by rfl⟩ : syracuseStep 1107841 = 830881) (by norm_num)
theorem B2221973 : Blo 984595 2221973 := bbase (se 6 (by rfl) ⟨52077, by rfl⟩ : syracuseStep 2221973 = 104155) (by norm_num)
theorem B1107877 : Blo 984595 1107877 := bbase (se 4 (by rfl) ⟨103863, by rfl⟩ : syracuseStep 1107877 = 207727) (by norm_num)
theorem B1664941 : Blo 984595 1664941 := bbase (se 3 (by rfl) ⟨312176, by rfl⟩ : syracuseStep 1664941 = 624353) (by norm_num)
theorem B1107913 : Blo 984595 1107913 := bbase (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) (by norm_num)
theorem B1140689 : Blo 984595 1140689 := bbase (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) (by norm_num)
theorem B2222045 : Blo 984595 2222045 := bbase (se 3 (by rfl) ⟨416633, by rfl⟩ : syracuseStep 2222045 = 833267) (by norm_num)
theorem B1107949 : Blo 984595 1107949 := bbase (se 3 (by rfl) ⟨207740, by rfl⟩ : syracuseStep 1107949 = 415481) (by norm_num)
theorem B1665029 : Blo 984595 1665029 := bbase (se 4 (by rfl) ⟨156096, by rfl⟩ : syracuseStep 1665029 = 312193) (by norm_num)
theorem B1107985 : Blo 984595 1107985 := bbase (se 2 (by rfl) ⟨415494, by rfl⟩ : syracuseStep 1107985 = 830989) (by norm_num)
theorem B2222117 : Blo 984595 2222117 := bbase (se 4 (by rfl) ⟨208323, by rfl⟩ : syracuseStep 2222117 = 416647) (by norm_num)
theorem B1108021 : Blo 984595 1108021 := bbase (se 5 (by rfl) ⟨51938, by rfl⟩ : syracuseStep 1108021 = 103877) (by norm_num)
theorem B1108057 : Blo 984595 1108057 := bbase (se 2 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 1108057 = 831043) (by norm_num)
theorem B2222189 : Blo 984595 2222189 := bbase (se 3 (by rfl) ⟨416660, by rfl⟩ : syracuseStep 2222189 = 833321) (by norm_num)
theorem B1108093 : Blo 984595 1108093 := bbase (se 3 (by rfl) ⟨207767, by rfl⟩ : syracuseStep 1108093 = 415535) (by norm_num)
theorem B1665157 : Blo 984595 1665157 := bbase (se 4 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 1665157 = 312217) (by norm_num)
theorem B1403029 : Blo 984595 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B1108129 : Blo 984595 1108129 := bbase (se 2 (by rfl) ⟨415548, by rfl⟩ : syracuseStep 1108129 = 831097) (by norm_num)
theorem B2222261 : Blo 984595 2222261 := bbase (se 5 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 2222261 = 208337) (by norm_num)
theorem B1108165 : Blo 984595 1108165 := bbase (se 4 (by rfl) ⟨103890, by rfl⟩ : syracuseStep 1108165 = 207781) (by norm_num)
theorem B3336389 : Blo 984595 3336389 := bbase (se 4 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 3336389 = 625573) (by norm_num)
theorem B1665245 : Blo 984595 1665245 := bbase (se 3 (by rfl) ⟨312233, by rfl⟩ : syracuseStep 1665245 = 624467) (by norm_num)
theorem B1108201 : Blo 984595 1108201 := bbase (se 2 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 1108201 = 831151) (by norm_num)
theorem B2222333 : Blo 984595 2222333 := bbase (se 3 (by rfl) ⟨416687, by rfl⟩ : syracuseStep 2222333 = 833375) (by norm_num)
theorem B1108237 : Blo 984595 1108237 := bbase (se 3 (by rfl) ⟨207794, by rfl⟩ : syracuseStep 1108237 = 415589) (by norm_num)
theorem B1108273 : Blo 984595 1108273 := bbase (se 2 (by rfl) ⟨415602, by rfl⟩ : syracuseStep 1108273 = 831205) (by norm_num)
theorem B2222405 : Blo 984595 2222405 := bbase (se 4 (by rfl) ⟨208350, by rfl⟩ : syracuseStep 2222405 = 416701) (by norm_num)
theorem B1108309 : Blo 984595 1108309 := bbase (se 10 (by rfl) ⟨1623, by rfl⟩ : syracuseStep 1108309 = 3247) (by norm_num)
theorem B1665373 : Blo 984595 1665373 := bbase (se 3 (by rfl) ⟨312257, by rfl⟩ : syracuseStep 1665373 = 624515) (by norm_num)
theorem B1108345 : Blo 984595 1108345 := bbase (se 2 (by rfl) ⟨415629, by rfl⟩ : syracuseStep 1108345 = 831259) (by norm_num)
theorem B2222477 : Blo 984595 2222477 := bbase (se 3 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 2222477 = 833429) (by norm_num)
theorem B1108381 : Blo 984595 1108381 := bbase (se 3 (by rfl) ⟨207821, by rfl⟩ : syracuseStep 1108381 = 415643) (by norm_num)
theorem B1665461 : Blo 984595 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B1108417 : Blo 984595 1108417 := bbase (se 2 (by rfl) ⟨415656, by rfl⟩ : syracuseStep 1108417 = 831313) (by norm_num)
theorem B2222549 : Blo 984595 2222549 := bbase (se 7 (by rfl) ⟨26045, by rfl⟩ : syracuseStep 2222549 = 52091) (by norm_num)
theorem B1108453 : Blo 984595 1108453 := bbase (se 4 (by rfl) ⟨103917, by rfl⟩ : syracuseStep 1108453 = 207835) (by norm_num)
theorem B1108489 : Blo 984595 1108489 := bbase (se 2 (by rfl) ⟨415683, by rfl⟩ : syracuseStep 1108489 = 831367) (by norm_num)
theorem B2222621 : Blo 984595 2222621 := bbase (se 3 (by rfl) ⟨416741, by rfl⟩ : syracuseStep 2222621 = 833483) (by norm_num)
theorem B1108525 : Blo 984595 1108525 := bbase (se 3 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 1108525 = 415697) (by norm_num)
theorem B1665589 : Blo 984595 1665589 := bbase (se 5 (by rfl) ⟨78074, by rfl⟩ : syracuseStep 1665589 = 156149) (by norm_num)
theorem B1108561 : Blo 984595 1108561 := bbase (se 2 (by rfl) ⟨415710, by rfl⟩ : syracuseStep 1108561 = 831421) (by norm_num)
theorem B2222693 : Blo 984595 2222693 := bbase (se 4 (by rfl) ⟨208377, by rfl⟩ : syracuseStep 2222693 = 416755) (by norm_num)
theorem B1108597 : Blo 984595 1108597 := bbase (se 5 (by rfl) ⟨51965, by rfl⟩ : syracuseStep 1108597 = 103931) (by norm_num)
theorem B1665677 : Blo 984595 1665677 := bbase (se 3 (by rfl) ⟨312314, by rfl⟩ : syracuseStep 1665677 = 624629) (by norm_num)
theorem B1108633 : Blo 984595 1108633 := bbase (se 2 (by rfl) ⟨415737, by rfl⟩ : syracuseStep 1108633 = 831475) (by norm_num)
theorem B2222765 : Blo 984595 2222765 := bbase (se 3 (by rfl) ⟨416768, by rfl⟩ : syracuseStep 2222765 = 833537) (by norm_num)
theorem B1108669 : Blo 984595 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B1108705 : Blo 984595 1108705 := bbase (se 2 (by rfl) ⟨415764, by rfl⟩ : syracuseStep 1108705 = 831529) (by norm_num)
theorem B2222837 : Blo 984595 2222837 := bbase (se 5 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 2222837 = 208391) (by norm_num)
theorem B1108741 : Blo 984595 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B1665805 : Blo 984595 1665805 := bbase (se 3 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 1665805 = 624677) (by norm_num)
theorem B1108777 : Blo 984595 1108777 := bbase (se 2 (by rfl) ⟨415791, by rfl⟩ : syracuseStep 1108777 = 831583) (by norm_num)
theorem B2222909 : Blo 984595 2222909 := bbase (se 3 (by rfl) ⟨416795, by rfl⟩ : syracuseStep 2222909 = 833591) (by norm_num)
theorem B1108813 : Blo 984595 1108813 := bbase (se 3 (by rfl) ⟨207902, by rfl⟩ : syracuseStep 1108813 = 415805) (by norm_num)
theorem B1665893 : Blo 984595 1665893 := bbase (se 4 (by rfl) ⟨156177, by rfl⟩ : syracuseStep 1665893 = 312355) (by norm_num)
theorem B1108849 : Blo 984595 1108849 := bbase (se 2 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 1108849 = 831637) (by norm_num)
theorem B2222981 : Blo 984595 2222981 := bbase (se 4 (by rfl) ⟨208404, by rfl⟩ : syracuseStep 2222981 = 416809) (by norm_num)
theorem B1108885 : Blo 984595 1108885 := bbase (se 6 (by rfl) ⟨25989, by rfl⟩ : syracuseStep 1108885 = 51979) (by norm_num)
theorem B1403821 : Blo 984595 1403821 := bbase (se 3 (by rfl) ⟨263216, by rfl⟩ : syracuseStep 1403821 = 526433) (by norm_num)
theorem B1108921 : Blo 984595 1108921 := bbase (se 2 (by rfl) ⟨415845, by rfl⟩ : syracuseStep 1108921 = 831691) (by norm_num)
theorem B2223053 : Blo 984595 2223053 := bbase (se 3 (by rfl) ⟨416822, by rfl⟩ : syracuseStep 2223053 = 833645) (by norm_num)
theorem B1108957 : Blo 984595 1108957 := bbase (se 3 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 1108957 = 415859) (by norm_num)
theorem B1666021 : Blo 984595 1666021 := bbase (se 4 (by rfl) ⟨156189, by rfl⟩ : syracuseStep 1666021 = 312379) (by norm_num)
theorem B1108993 : Blo 984595 1108993 := bbase (se 2 (by rfl) ⟨415872, by rfl⟩ : syracuseStep 1108993 = 831745) (by norm_num)
theorem B2223125 : Blo 984595 2223125 := bbase (se 6 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 2223125 = 104209) (by norm_num)
theorem B1109029 : Blo 984595 1109029 := bbase (se 4 (by rfl) ⟨103971, by rfl⟩ : syracuseStep 1109029 = 207943) (by norm_num)
theorem B4221989 : Blo 984595 4221989 := bbase (se 4 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 4221989 = 791623) (by norm_num)
theorem B1666109 : Blo 984595 1666109 := bbase (se 3 (by rfl) ⟨312395, by rfl⟩ : syracuseStep 1666109 = 624791) (by norm_num)
theorem B1109065 : Blo 984595 1109065 := bbase (se 2 (by rfl) ⟨415899, by rfl⟩ : syracuseStep 1109065 = 831799) (by norm_num)
theorem B2223197 : Blo 984595 2223197 := bbase (se 3 (by rfl) ⟨416849, by rfl⟩ : syracuseStep 2223197 = 833699) (by norm_num)
theorem B1109101 : Blo 984595 1109101 := bbase (se 3 (by rfl) ⟨207956, by rfl⟩ : syracuseStep 1109101 = 415913) (by norm_num)
theorem B1109137 : Blo 984595 1109137 := bbase (se 2 (by rfl) ⟨415926, by rfl⟩ : syracuseStep 1109137 = 831853) (by norm_num)
theorem B2223269 : Blo 984595 2223269 := bbase (se 4 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 2223269 = 416863) (by norm_num)
theorem B1109173 : Blo 984595 1109173 := bbase (se 5 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 1109173 = 103985) (by norm_num)
theorem B1666237 : Blo 984595 1666237 := bbase (se 3 (by rfl) ⟨312419, by rfl⟩ : syracuseStep 1666237 = 624839) (by norm_num)
theorem B6745301 : Blo 984595 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B1109209 : Blo 984595 1109209 := bbase (se 2 (by rfl) ⟨415953, by rfl⟩ : syracuseStep 1109209 = 831907) (by norm_num)
theorem B2223341 : Blo 984595 2223341 := bbase (se 3 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 2223341 = 833753) (by norm_num)
theorem B1109245 : Blo 984595 1109245 := bbase (se 3 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 1109245 = 415967) (by norm_num)
theorem B1404157 : Blo 984595 1404157 := bbase (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) (by norm_num)
theorem B1666325 : Blo 984595 1666325 := bbase (se 6 (by rfl) ⟨39054, by rfl⟩ : syracuseStep 1666325 = 78109) (by norm_num)
theorem B1109281 : Blo 984595 1109281 := bbase (se 2 (by rfl) ⟨415980, by rfl⟩ : syracuseStep 1109281 = 831961) (by norm_num)
theorem B2223413 : Blo 984595 2223413 := bbase (se 5 (by rfl) ⟨104222, by rfl⟩ : syracuseStep 2223413 = 208445) (by norm_num)
theorem B1109317 : Blo 984595 1109317 := bbase (se 4 (by rfl) ⟨103998, by rfl⟩ : syracuseStep 1109317 = 207997) (by norm_num)
theorem B4222277 : Blo 984595 4222277 := bbase (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) (by norm_num)
theorem B1109353 : Blo 984595 1109353 := bbase (se 2 (by rfl) ⟨416007, by rfl⟩ : syracuseStep 1109353 = 832015) (by norm_num)
theorem B2223485 : Blo 984595 2223485 := bbase (se 3 (by rfl) ⟨416903, by rfl⟩ : syracuseStep 2223485 = 833807) (by norm_num)
theorem B1109389 : Blo 984595 1109389 := bbase (se 3 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 1109389 = 416021) (by norm_num)
theorem B1666453 : Blo 984595 1666453 := bbase (se 6 (by rfl) ⟨39057, by rfl⟩ : syracuseStep 1666453 = 78115) (by norm_num)
theorem B1109425 : Blo 984595 1109425 := bbase (se 2 (by rfl) ⟨416034, by rfl⟩ : syracuseStep 1109425 = 832069) (by norm_num)
theorem B2223557 : Blo 984595 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B1109461 : Blo 984595 1109461 := bbase (se 7 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 1109461 = 26003) (by norm_num)
theorem B1404373 : Blo 984595 1404373 := bbase (se 7 (by rfl) ⟨16457, by rfl⟩ : syracuseStep 1404373 = 32915) (by norm_num)
theorem B1666541 : Blo 984595 1666541 := bbase (se 3 (by rfl) ⟨312476, by rfl⟩ : syracuseStep 1666541 = 624953) (by norm_num)
theorem B1109497 : Blo 984595 1109497 := bbase (se 2 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 1109497 = 832123) (by norm_num)
theorem B2223629 : Blo 984595 2223629 := bbase (se 3 (by rfl) ⟨416930, by rfl⟩ : syracuseStep 2223629 = 833861) (by norm_num)
theorem B1109533 : Blo 984595 1109533 := bbase (se 3 (by rfl) ⟨208037, by rfl⟩ : syracuseStep 1109533 = 416075) (by norm_num)
theorem B1109569 : Blo 984595 1109569 := bbase (se 2 (by rfl) ⟨416088, by rfl⟩ : syracuseStep 1109569 = 832177) (by norm_num)
theorem B2223701 : Blo 984595 2223701 := bbase (se 8 (by rfl) ⟨13029, by rfl⟩ : syracuseStep 2223701 = 26059) (by norm_num)
theorem B1109605 : Blo 984595 1109605 := bbase (se 4 (by rfl) ⟨104025, by rfl⟩ : syracuseStep 1109605 = 208051) (by norm_num)
theorem B1666669 : Blo 984595 1666669 := bbase (se 3 (by rfl) ⟨312500, by rfl⟩ : syracuseStep 1666669 = 625001) (by norm_num)
theorem B1109641 : Blo 984595 1109641 := bbase (se 2 (by rfl) ⟨416115, by rfl⟩ : syracuseStep 1109641 = 832231) (by norm_num)
theorem B11398805 : Blo 984595 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B2223773 : Blo 984595 2223773 := bbase (se 3 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 2223773 = 833915) (by norm_num)
theorem B1109677 : Blo 984595 1109677 := bbase (se 3 (by rfl) ⟨208064, by rfl⟩ : syracuseStep 1109677 = 416129) (by norm_num)
theorem B1666757 : Blo 984595 1666757 := bbase (se 4 (by rfl) ⟨156258, by rfl⟩ : syracuseStep 1666757 = 312517) (by norm_num)
theorem B1109713 : Blo 984595 1109713 := bbase (se 2 (by rfl) ⟨416142, by rfl⟩ : syracuseStep 1109713 = 832285) (by norm_num)
theorem B2223845 : Blo 984595 2223845 := bbase (se 4 (by rfl) ⟨208485, by rfl⟩ : syracuseStep 2223845 = 416971) (by norm_num)
theorem B1109749 : Blo 984595 1109749 := bbase (se 5 (by rfl) ⟨52019, by rfl⟩ : syracuseStep 1109749 = 104039) (by norm_num)
theorem B1109785 : Blo 984595 1109785 := bbase (se 2 (by rfl) ⟨416169, by rfl⟩ : syracuseStep 1109785 = 832339) (by norm_num)
theorem B2223917 : Blo 984595 2223917 := bbase (se 3 (by rfl) ⟨416984, by rfl⟩ : syracuseStep 2223917 = 833969) (by norm_num)
theorem B1109821 : Blo 984595 1109821 := bbase (se 3 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 1109821 = 416183) (by norm_num)
theorem B1666885 : Blo 984595 1666885 := bbase (se 4 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 1666885 = 312541) (by norm_num)
theorem B1404749 : Blo 984595 1404749 := bbase (se 3 (by rfl) ⟨263390, by rfl⟩ : syracuseStep 1404749 = 526781) (by norm_num)
theorem B1109857 : Blo 984595 1109857 := bbase (se 2 (by rfl) ⟨416196, by rfl⟩ : syracuseStep 1109857 = 832393) (by norm_num)
theorem B2223989 : Blo 984595 2223989 := bbase (se 5 (by rfl) ⟨104249, by rfl⟩ : syracuseStep 2223989 = 208499) (by norm_num)
theorem B1109893 : Blo 984595 1109893 := bbase (se 4 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 1109893 = 208105) (by norm_num)
theorem B1666973 : Blo 984595 1666973 := bbase (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) (by norm_num)
theorem B1109929 : Blo 984595 1109929 := bbase (se 2 (by rfl) ⟨416223, by rfl⟩ : syracuseStep 1109929 = 832447) (by norm_num)
theorem B2224061 : Blo 984595 2224061 := bbase (se 3 (by rfl) ⟨417011, by rfl⟩ : syracuseStep 2224061 = 834023) (by norm_num)
theorem B1109965 : Blo 984595 1109965 := bbase (se 3 (by rfl) ⟨208118, by rfl⟩ : syracuseStep 1109965 = 416237) (by norm_num)
theorem B1110001 : Blo 984595 1110001 := bbase (se 2 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 1110001 = 832501) (by norm_num)
theorem B2224133 : Blo 984595 2224133 := bbase (se 4 (by rfl) ⟨208512, by rfl⟩ : syracuseStep 2224133 = 417025) (by norm_num)
theorem B1110037 : Blo 984595 1110037 := bbase (se 6 (by rfl) ⟨26016, by rfl⟩ : syracuseStep 1110037 = 52033) (by norm_num)
theorem B1667101 : Blo 984595 1667101 := bbase (se 3 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 1667101 = 625163) (by norm_num)
theorem B1110073 : Blo 984595 1110073 := bbase (se 2 (by rfl) ⟨416277, by rfl⟩ : syracuseStep 1110073 = 832555) (by norm_num)
theorem B2224205 : Blo 984595 2224205 := bbase (se 3 (by rfl) ⟨417038, by rfl⟩ : syracuseStep 2224205 = 834077) (by norm_num)
theorem B1110109 : Blo 984595 1110109 := bbase (se 3 (by rfl) ⟨208145, by rfl⟩ : syracuseStep 1110109 = 416291) (by norm_num)
theorem B1667189 : Blo 984595 1667189 := bbase (se 5 (by rfl) ⟨78149, by rfl⟩ : syracuseStep 1667189 = 156299) (by norm_num)
theorem B1110145 : Blo 984595 1110145 := bbase (se 2 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 1110145 = 832609) (by norm_num)
theorem B2224277 : Blo 984595 2224277 := bbase (se 6 (by rfl) ⟨52131, by rfl⟩ : syracuseStep 2224277 = 104263) (by norm_num)
theorem B1110181 : Blo 984595 1110181 := bbase (se 4 (by rfl) ⟨104079, by rfl⟩ : syracuseStep 1110181 = 208159) (by norm_num)
theorem B1110217 : Blo 984595 1110217 := bbase (se 2 (by rfl) ⟨416331, by rfl⟩ : syracuseStep 1110217 = 832663) (by norm_num)
theorem B13693141 : Blo 984595 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B1110253 : Blo 984595 1110253 := bbase (se 3 (by rfl) ⟨208172, by rfl⟩ : syracuseStep 1110253 = 416345) (by norm_num)
theorem B1667317 : Blo 984595 1667317 := bbase (se 5 (by rfl) ⟨78155, by rfl⟩ : syracuseStep 1667317 = 156311) (by norm_num)
theorem B1110289 : Blo 984595 1110289 := bbase (se 2 (by rfl) ⟨416358, by rfl⟩ : syracuseStep 1110289 = 832717) (by norm_num)
theorem B1110325 : Blo 984595 1110325 := bbase (se 5 (by rfl) ⟨52046, by rfl⟩ : syracuseStep 1110325 = 104093) (by norm_num)
theorem B1667405 : Blo 984595 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B1110361 : Blo 984595 1110361 := bbase (se 2 (by rfl) ⟨416385, by rfl⟩ : syracuseStep 1110361 = 832771) (by norm_num)
theorem B1110397 : Blo 984595 1110397 := bbase (se 3 (by rfl) ⟨208199, by rfl⟩ : syracuseStep 1110397 = 416399) (by norm_num)
theorem B1110433 : Blo 984595 1110433 := bbase (se 2 (by rfl) ⟨416412, by rfl⟩ : syracuseStep 1110433 = 832825) (by norm_num)
theorem B1110469 : Blo 984595 1110469 := bbase (se 4 (by rfl) ⟨104106, by rfl⟩ : syracuseStep 1110469 = 208213) (by norm_num)
theorem B1667533 : Blo 984595 1667533 := bbase (se 3 (by rfl) ⟨312662, by rfl⟩ : syracuseStep 1667533 = 625325) (by norm_num)
theorem B1110505 : Blo 984595 1110505 := bbase (se 2 (by rfl) ⟨416439, by rfl⟩ : syracuseStep 1110505 = 832879) (by norm_num)
theorem B1110541 : Blo 984595 1110541 := bbase (se 3 (by rfl) ⟨208226, by rfl⟩ : syracuseStep 1110541 = 416453) (by norm_num)
theorem B1667621 : Blo 984595 1667621 := bbase (se 4 (by rfl) ⟨156339, by rfl⟩ : syracuseStep 1667621 = 312679) (by norm_num)
theorem B1110577 : Blo 984595 1110577 := bbase (se 2 (by rfl) ⟨416466, by rfl⟩ : syracuseStep 1110577 = 832933) (by norm_num)
theorem B2814533 : Blo 984595 2814533 := bbase (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) (by norm_num)
theorem B1110613 : Blo 984595 1110613 := bbase (se 8 (by rfl) ⟨6507, by rfl⟩ : syracuseStep 1110613 = 13015) (by norm_num)
theorem B1110649 : Blo 984595 1110649 := bbase (se 2 (by rfl) ⟨416493, by rfl⟩ : syracuseStep 1110649 = 832987) (by norm_num)
theorem B4747909 : Blo 984595 4747909 := bbase (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) (by norm_num)
theorem B7500437 : Blo 984595 7500437 := bbase (se 6 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 7500437 = 351583) (by norm_num)
theorem B1110685 : Blo 984595 1110685 := bbase (se 3 (by rfl) ⟨208253, by rfl⟩ : syracuseStep 1110685 = 416507) (by norm_num)
theorem B1667749 : Blo 984595 1667749 := bbase (se 4 (by rfl) ⟨156351, by rfl⟩ : syracuseStep 1667749 = 312703) (by norm_num)
theorem B1110721 : Blo 984595 1110721 := bbase (se 2 (by rfl) ⟨416520, by rfl⟩ : syracuseStep 1110721 = 833041) (by norm_num)
theorem B8418005 : Blo 984595 8418005 := bbase (se 7 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 8418005 = 197297) (by norm_num)
theorem B1110757 : Blo 984595 1110757 := bbase (se 4 (by rfl) ⟨104133, by rfl⟩ : syracuseStep 1110757 = 208267) (by norm_num)
theorem B1667837 : Blo 984595 1667837 := bbase (se 3 (by rfl) ⟨312719, by rfl⟩ : syracuseStep 1667837 = 625439) (by norm_num)
theorem B3994373 : Blo 984595 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B1110793 : Blo 984595 1110793 := bbase (se 2 (by rfl) ⟨416547, by rfl⟩ : syracuseStep 1110793 = 833095) (by norm_num)
theorem B1110829 : Blo 984595 1110829 := bbase (se 3 (by rfl) ⟨208280, by rfl⟩ : syracuseStep 1110829 = 416561) (by norm_num)
theorem B1110865 : Blo 984595 1110865 := bbase (se 2 (by rfl) ⟨416574, by rfl⟩ : syracuseStep 1110865 = 833149) (by norm_num)
theorem B1110901 : Blo 984595 1110901 := bbase (se 5 (by rfl) ⟨52073, by rfl⟩ : syracuseStep 1110901 = 104147) (by norm_num)
theorem B1667965 : Blo 984595 1667965 := bbase (se 3 (by rfl) ⟨312743, by rfl⟩ : syracuseStep 1667965 = 625487) (by norm_num)
theorem B1110937 : Blo 984595 1110937 := bbase (se 2 (by rfl) ⟨416601, by rfl⟩ : syracuseStep 1110937 = 833203) (by norm_num)
theorem B1110973 : Blo 984595 1110973 := bbase (se 3 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 1110973 = 416615) (by norm_num)
theorem B1668053 : Blo 984595 1668053 := bbase (se 7 (by rfl) ⟨19547, by rfl⟩ : syracuseStep 1668053 = 39095) (by norm_num)
theorem B9630677 : Blo 984595 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B1111009 : Blo 984595 1111009 := bbase (se 2 (by rfl) ⟨416628, by rfl⟩ : syracuseStep 1111009 = 833257) (by norm_num)
theorem B1111045 : Blo 984595 1111045 := bbase (se 4 (by rfl) ⟨104160, by rfl⟩ : syracuseStep 1111045 = 208321) (by norm_num)
theorem B1111081 : Blo 984595 1111081 := bbase (se 2 (by rfl) ⟨416655, by rfl⟩ : syracuseStep 1111081 = 833311) (by norm_num)
theorem B1111117 : Blo 984595 1111117 := bbase (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) (by norm_num)
theorem B1668181 : Blo 984595 1668181 := bbase (se 8 (by rfl) ⟨9774, by rfl⟩ : syracuseStep 1668181 = 19549) (by norm_num)
theorem B1111153 : Blo 984595 1111153 := bbase (se 2 (by rfl) ⟨416682, by rfl⟩ : syracuseStep 1111153 = 833365) (by norm_num)
theorem B1111189 : Blo 984595 1111189 := bbase (se 6 (by rfl) ⟨26043, by rfl⟩ : syracuseStep 1111189 = 52087) (by norm_num)
theorem B1111225 : Blo 984595 1111225 := bbase (se 2 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 1111225 = 833419) (by norm_num)
theorem B1406173 : Blo 984595 1406173 := bbase (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) (by norm_num)
theorem B1111261 : Blo 984595 1111261 := bbase (se 3 (by rfl) ⟨208361, by rfl⟩ : syracuseStep 1111261 = 416723) (by norm_num)
theorem B9860341 : Blo 984595 9860341 := bbase (se 5 (by rfl) ⟨462203, by rfl⟩ : syracuseStep 9860341 = 924407) (by norm_num)
theorem B1111297 : Blo 984595 1111297 := bbase (se 2 (by rfl) ⟨416736, by rfl⟩ : syracuseStep 1111297 = 833473) (by norm_num)
theorem B1111333 : Blo 984595 1111333 := bbase (se 4 (by rfl) ⟨104187, by rfl⟩ : syracuseStep 1111333 = 208375) (by norm_num)
theorem B1111369 : Blo 984595 1111369 := bbase (se 2 (by rfl) ⟨416763, by rfl⟩ : syracuseStep 1111369 = 833527) (by norm_num)
theorem B1111405 : Blo 984595 1111405 := bbase (se 3 (by rfl) ⟨208388, by rfl⟩ : syracuseStep 1111405 = 416777) (by norm_num)
theorem B1111441 : Blo 984595 1111441 := bbase (se 2 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 1111441 = 833581) (by norm_num)
theorem B1111477 : Blo 984595 1111477 := bbase (se 5 (by rfl) ⟨52100, by rfl⟩ : syracuseStep 1111477 = 104201) (by norm_num)
theorem B1111513 : Blo 984595 1111513 := bbase (se 2 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 1111513 = 833635) (by norm_num)
theorem B1111549 : Blo 984595 1111549 := bbase (se 3 (by rfl) ⟨208415, by rfl⟩ : syracuseStep 1111549 = 416831) (by norm_num)
theorem B1111585 : Blo 984595 1111585 := bbase (se 2 (by rfl) ⟨416844, by rfl⟩ : syracuseStep 1111585 = 833689) (by norm_num)
theorem B1111621 : Blo 984595 1111621 := bbase (se 4 (by rfl) ⟨104214, by rfl⟩ : syracuseStep 1111621 = 208429) (by norm_num)
theorem B1111657 : Blo 984595 1111657 := bbase (se 2 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 1111657 = 833743) (by norm_num)
theorem B1898101 : Blo 984595 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B1111693 : Blo 984595 1111693 := bbase (se 3 (by rfl) ⟨208442, by rfl⟩ : syracuseStep 1111693 = 416885) (by norm_num)
theorem B1111729 : Blo 984595 1111729 := bbase (se 2 (by rfl) ⟨416898, by rfl⟩ : syracuseStep 1111729 = 833797) (by norm_num)
theorem B1111765 : Blo 984595 1111765 := bbase (se 7 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 1111765 = 26057) (by norm_num)
theorem B1603309 : Blo 984595 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B1111801 : Blo 984595 1111801 := bbase (se 2 (by rfl) ⟨416925, by rfl⟩ : syracuseStep 1111801 = 833851) (by norm_num)
theorem B1111837 : Blo 984595 1111837 := bbase (se 3 (by rfl) ⟨208469, by rfl⟩ : syracuseStep 1111837 = 416939) (by norm_num)
theorem B1406765 : Blo 984595 1406765 := bbase (se 3 (by rfl) ⟨263768, by rfl⟩ : syracuseStep 1406765 = 527537) (by norm_num)
theorem B1111873 : Blo 984595 1111873 := bbase (se 2 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 1111873 = 833905) (by norm_num)
theorem B1111909 : Blo 984595 1111909 := bbase (se 4 (by rfl) ⟨104241, by rfl⟩ : syracuseStep 1111909 = 208483) (by norm_num)
theorem B1406845 : Blo 984595 1406845 := bbase (se 3 (by rfl) ⟨263783, by rfl⟩ : syracuseStep 1406845 = 527567) (by norm_num)
theorem B1111945 : Blo 984595 1111945 := bbase (se 2 (by rfl) ⟨416979, by rfl⟩ : syracuseStep 1111945 = 833959) (by norm_num)
theorem B1111981 : Blo 984595 1111981 := bbase (se 3 (by rfl) ⟨208496, by rfl⟩ : syracuseStep 1111981 = 416993) (by norm_num)
theorem B1112017 : Blo 984595 1112017 := bbase (se 2 (by rfl) ⟨417006, by rfl⟩ : syracuseStep 1112017 = 834013) (by norm_num)
theorem B1406965 : Blo 984595 1406965 := bbase (se 5 (by rfl) ⟨65951, by rfl⟩ : syracuseStep 1406965 = 131903) (by norm_num)
theorem B1112053 : Blo 984595 1112053 := bbase (se 5 (by rfl) ⟨52127, by rfl⟩ : syracuseStep 1112053 = 104255) (by norm_num)
theorem B1112089 : Blo 984595 1112089 := bbase (se 2 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 1112089 = 834067) (by norm_num)
theorem B1112125 : Blo 984595 1112125 := bbase (se 3 (by rfl) ⟨208523, by rfl⟩ : syracuseStep 1112125 = 417047) (by norm_num)
theorem B1407061 : Blo 984595 1407061 := bbase (se 8 (by rfl) ⟨8244, by rfl⟩ : syracuseStep 1407061 = 16489) (by norm_num)
theorem B1112161 : Blo 984595 1112161 := bbase (se 2 (by rfl) ⟨417060, by rfl⟩ : syracuseStep 1112161 = 834121) (by norm_num)
theorem B12024085 : Blo 984595 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B1898845 : Blo 984595 1898845 := bbase (se 3 (by rfl) ⟨356033, by rfl⟩ : syracuseStep 1898845 = 712067) (by norm_num)
theorem B6322549 : Blo 984595 6322549 := bbase (se 5 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 6322549 = 592739) (by norm_num)
theorem B4323797 : Blo 984595 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B1407557 : Blo 984595 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1604437 : Blo 984595 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B3799973 : Blo 984595 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B11369429 : Blo 984595 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B1997893 : Blo 984595 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B4554245 : Blo 984595 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B1900525 : Blo 984595 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B1900817 : Blo 984595 1900817 := bstep (se 2 (by rfl) ⟨712806, by rfl⟩ : syracuseStep 1900817 = 1425613) B1425613
theorem B7504325 : Blo 984595 7504325 := bstep (se 4 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 7504325 = 1407061) B1407061
theorem B8422001 : Blo 984595 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B1802947 : Blo 984595 1802947 := bstep (se 1 (by rfl) ⟨1352210, by rfl⟩ : syracuseStep 1802947 = 2704421) B2704421
theorem B1999619 : Blo 984595 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B1999651 : Blo 984595 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B2163665 : Blo 984595 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B1246195 : Blo 984595 1246195 := bstep (se 1 (by rfl) ⟨934646, by rfl⟩ : syracuseStep 1246195 = 1869293) B1869293
theorem B3376163 : Blo 984595 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B1246691 : Blo 984595 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B984595 : Blo 984595 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B984611 : Blo 984595 984611 := bstep (se 1 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 984611 = 1476917) B1476917
theorem B984627 : Blo 984595 984627 := bstep (se 1 (by rfl) ⟨738470, by rfl⟩ : syracuseStep 984627 = 1476941) B1476941
theorem B984643 : Blo 984595 984643 := bstep (se 1 (by rfl) ⟨738482, by rfl⟩ : syracuseStep 984643 = 1476965) B1476965
theorem B984659 : Blo 984595 984659 := bstep (se 1 (by rfl) ⟨738494, by rfl⟩ : syracuseStep 984659 = 1476989) B1476989
theorem B984675 : Blo 984595 984675 := bstep (se 1 (by rfl) ⟨738506, by rfl⟩ : syracuseStep 984675 = 1477013) B1477013
theorem B984691 : Blo 984595 984691 := bstep (se 1 (by rfl) ⟨738518, by rfl⟩ : syracuseStep 984691 = 1477037) B1477037
theorem B984707 : Blo 984595 984707 := bstep (se 1 (by rfl) ⟨738530, by rfl⟩ : syracuseStep 984707 = 1477061) B1477061
theorem B984723 : Blo 984595 984723 := bstep (se 1 (by rfl) ⟨738542, by rfl⟩ : syracuseStep 984723 = 1477085) B1477085
theorem B984739 : Blo 984595 984739 := bstep (se 1 (by rfl) ⟨738554, by rfl⟩ : syracuseStep 984739 = 1477109) B1477109
theorem B1869475 : Blo 984595 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B984755 : Blo 984595 984755 := bstep (se 1 (by rfl) ⟨738566, by rfl⟩ : syracuseStep 984755 = 1477133) B1477133
theorem B984771 : Blo 984595 984771 := bstep (se 1 (by rfl) ⟨738578, by rfl⟩ : syracuseStep 984771 = 1477157) B1477157
theorem B984787 : Blo 984595 984787 := bstep (se 1 (by rfl) ⟨738590, by rfl⟩ : syracuseStep 984787 = 1477181) B1477181
theorem B984803 : Blo 984595 984803 := bstep (se 1 (by rfl) ⟨738602, by rfl⟩ : syracuseStep 984803 = 1477205) B1477205
theorem B984819 : Blo 984595 984819 := bstep (se 1 (by rfl) ⟨738614, by rfl⟩ : syracuseStep 984819 = 1477229) B1477229
theorem B984835 : Blo 984595 984835 := bstep (se 1 (by rfl) ⟨738626, by rfl⟩ : syracuseStep 984835 = 1477253) B1477253
theorem B5998349 : Blo 984595 5998349 := bstep (se 3 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 5998349 = 2249381) B2249381
theorem B2000657 : Blo 984595 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B984851 : Blo 984595 984851 := bstep (se 1 (by rfl) ⟨738638, by rfl⟩ : syracuseStep 984851 = 1477277) B1477277
theorem B984867 : Blo 984595 984867 := bstep (se 1 (by rfl) ⟨738650, by rfl⟩ : syracuseStep 984867 = 1477301) B1477301
theorem B984883 : Blo 984595 984883 := bstep (se 1 (by rfl) ⟨738662, by rfl⟩ : syracuseStep 984883 = 1477325) B1477325
theorem B1869635 : Blo 984595 1869635 := bstep (se 1 (by rfl) ⟨1402226, by rfl⟩ : syracuseStep 1869635 = 2804453) B2804453
theorem B984899 : Blo 984595 984899 := bstep (se 1 (by rfl) ⟨738674, by rfl⟩ : syracuseStep 984899 = 1477349) B1477349
theorem B984915 : Blo 984595 984915 := bstep (se 1 (by rfl) ⟨738686, by rfl⟩ : syracuseStep 984915 = 1477373) B1477373
theorem B984931 : Blo 984595 984931 := bstep (se 1 (by rfl) ⟨738698, by rfl⟩ : syracuseStep 984931 = 1477397) B1477397
theorem B984947 : Blo 984595 984947 := bstep (se 1 (by rfl) ⟨738710, by rfl⟩ : syracuseStep 984947 = 1477421) B1477421
theorem B984963 : Blo 984595 984963 := bstep (se 1 (by rfl) ⟨738722, by rfl⟩ : syracuseStep 984963 = 1477445) B1477445
theorem B984979 : Blo 984595 984979 := bstep (se 1 (by rfl) ⟨738734, by rfl⟩ : syracuseStep 984979 = 1477469) B1477469
theorem B984995 : Blo 984595 984995 := bstep (se 1 (by rfl) ⟨738746, by rfl⟩ : syracuseStep 984995 = 1477493) B1477493
theorem B985011 : Blo 984595 985011 := bstep (se 1 (by rfl) ⟨738758, by rfl⟩ : syracuseStep 985011 = 1477517) B1477517
theorem B985027 : Blo 984595 985027 := bstep (se 1 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 985027 = 1477541) B1477541
theorem B985043 : Blo 984595 985043 := bstep (se 1 (by rfl) ⟨738782, by rfl⟩ : syracuseStep 985043 = 1477565) B1477565
theorem B985059 : Blo 984595 985059 := bstep (se 1 (by rfl) ⟨738794, by rfl⟩ : syracuseStep 985059 = 1477589) B1477589
theorem B985075 : Blo 984595 985075 := bstep (se 1 (by rfl) ⟨738806, by rfl⟩ : syracuseStep 985075 = 1477613) B1477613
theorem B985091 : Blo 984595 985091 := bstep (se 1 (by rfl) ⟨738818, by rfl⟩ : syracuseStep 985091 = 1477637) B1477637
theorem B10651661 : Blo 984595 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B985107 : Blo 984595 985107 := bstep (se 1 (by rfl) ⟨738830, by rfl⟩ : syracuseStep 985107 = 1477661) B1477661
theorem B985123 : Blo 984595 985123 := bstep (se 1 (by rfl) ⟨738842, by rfl⟩ : syracuseStep 985123 = 1477685) B1477685
theorem B985139 : Blo 984595 985139 := bstep (se 1 (by rfl) ⟨738854, by rfl⟩ : syracuseStep 985139 = 1477709) B1477709
theorem B985155 : Blo 984595 985155 := bstep (se 1 (by rfl) ⟨738866, by rfl⟩ : syracuseStep 985155 = 1477733) B1477733
theorem B985171 : Blo 984595 985171 := bstep (se 1 (by rfl) ⟨738878, by rfl⟩ : syracuseStep 985171 = 1477757) B1477757
theorem B985187 : Blo 984595 985187 := bstep (se 1 (by rfl) ⟨738890, by rfl⟩ : syracuseStep 985187 = 1477781) B1477781
theorem B985203 : Blo 984595 985203 := bstep (se 1 (by rfl) ⟨738902, by rfl⟩ : syracuseStep 985203 = 1477805) B1477805
theorem B985219 : Blo 984595 985219 := bstep (se 1 (by rfl) ⟨738914, by rfl⟩ : syracuseStep 985219 = 1477829) B1477829
theorem B985235 : Blo 984595 985235 := bstep (se 1 (by rfl) ⟨738926, by rfl⟩ : syracuseStep 985235 = 1477853) B1477853
theorem B985251 : Blo 984595 985251 := bstep (se 1 (by rfl) ⟨738938, by rfl⟩ : syracuseStep 985251 = 1477877) B1477877
theorem B1247395 : Blo 984595 1247395 := bstep (se 1 (by rfl) ⟨935546, by rfl⟩ : syracuseStep 1247395 = 1871093) B1871093
theorem B985267 : Blo 984595 985267 := bstep (se 1 (by rfl) ⟨738950, by rfl⟩ : syracuseStep 985267 = 1477901) B1477901
theorem B985283 : Blo 984595 985283 := bstep (se 1 (by rfl) ⟨738962, by rfl⟩ : syracuseStep 985283 = 1477925) B1477925
theorem B985299 : Blo 984595 985299 := bstep (se 1 (by rfl) ⟨738974, by rfl⟩ : syracuseStep 985299 = 1477949) B1477949
theorem B985315 : Blo 984595 985315 := bstep (se 1 (by rfl) ⟨738986, by rfl⟩ : syracuseStep 985315 = 1477973) B1477973
theorem B985331 : Blo 984595 985331 := bstep (se 1 (by rfl) ⟨738998, by rfl⟩ : syracuseStep 985331 = 1477997) B1477997
theorem B985347 : Blo 984595 985347 := bstep (se 1 (by rfl) ⟨739010, by rfl⟩ : syracuseStep 985347 = 1478021) B1478021
theorem B1247491 : Blo 984595 1247491 := bstep (se 1 (by rfl) ⟨935618, by rfl⟩ : syracuseStep 1247491 = 1871237) B1871237
theorem B985363 : Blo 984595 985363 := bstep (se 1 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 985363 = 1478045) B1478045
theorem B1476899 : Blo 984595 1476899 := bstep (se 1 (by rfl) ⟨1107674, by rfl⟩ : syracuseStep 1476899 = 2215349) B2215349
theorem B985379 : Blo 984595 985379 := bstep (se 1 (by rfl) ⟨739034, by rfl⟩ : syracuseStep 985379 = 1478069) B1478069
theorem B985395 : Blo 984595 985395 := bstep (se 1 (by rfl) ⟨739046, by rfl⟩ : syracuseStep 985395 = 1478093) B1478093
theorem B1476929 : Blo 984595 1476929 := bstep (se 2 (by rfl) ⟨553848, by rfl⟩ : syracuseStep 1476929 = 1107697) B1107697
theorem B985411 : Blo 984595 985411 := bstep (se 1 (by rfl) ⟨739058, by rfl⟩ : syracuseStep 985411 = 1478117) B1478117
theorem B1476947 : Blo 984595 1476947 := bstep (se 1 (by rfl) ⟨1107710, by rfl⟩ : syracuseStep 1476947 = 2215421) B2215421
theorem B985427 : Blo 984595 985427 := bstep (se 1 (by rfl) ⟨739070, by rfl⟩ : syracuseStep 985427 = 1478141) B1478141
theorem B985443 : Blo 984595 985443 := bstep (se 1 (by rfl) ⟨739082, by rfl⟩ : syracuseStep 985443 = 1478165) B1478165
theorem B1476977 : Blo 984595 1476977 := bstep (se 2 (by rfl) ⟨553866, by rfl⟩ : syracuseStep 1476977 = 1107733) B1107733
theorem B985459 : Blo 984595 985459 := bstep (se 1 (by rfl) ⟨739094, by rfl⟩ : syracuseStep 985459 = 1478189) B1478189
theorem B1476995 : Blo 984595 1476995 := bstep (se 1 (by rfl) ⟨1107746, by rfl⟩ : syracuseStep 1476995 = 2215493) B2215493
theorem B985475 : Blo 984595 985475 := bstep (se 1 (by rfl) ⟨739106, by rfl⟩ : syracuseStep 985475 = 1478213) B1478213
theorem B985491 : Blo 984595 985491 := bstep (se 1 (by rfl) ⟨739118, by rfl⟩ : syracuseStep 985491 = 1478237) B1478237
theorem B1477025 : Blo 984595 1477025 := bstep (se 2 (by rfl) ⟨553884, by rfl⟩ : syracuseStep 1477025 = 1107769) B1107769
theorem B985507 : Blo 984595 985507 := bstep (se 1 (by rfl) ⟨739130, by rfl⟩ : syracuseStep 985507 = 1478261) B1478261
theorem B1477043 : Blo 984595 1477043 := bstep (se 1 (by rfl) ⟨1107782, by rfl⟩ : syracuseStep 1477043 = 2215565) B2215565
theorem B985523 : Blo 984595 985523 := bstep (se 1 (by rfl) ⟨739142, by rfl⟩ : syracuseStep 985523 = 1478285) B1478285
theorem B985539 : Blo 984595 985539 := bstep (se 1 (by rfl) ⟨739154, by rfl⟩ : syracuseStep 985539 = 1478309) B1478309
theorem B1477073 : Blo 984595 1477073 := bstep (se 2 (by rfl) ⟨553902, by rfl⟩ : syracuseStep 1477073 = 1107805) B1107805
theorem B985555 : Blo 984595 985555 := bstep (se 1 (by rfl) ⟨739166, by rfl⟩ : syracuseStep 985555 = 1478333) B1478333
theorem B1477091 : Blo 984595 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B985571 : Blo 984595 985571 := bstep (se 1 (by rfl) ⟨739178, by rfl⟩ : syracuseStep 985571 = 1478357) B1478357
theorem B985587 : Blo 984595 985587 := bstep (se 1 (by rfl) ⟨739190, by rfl⟩ : syracuseStep 985587 = 1478381) B1478381
theorem B1477121 : Blo 984595 1477121 := bstep (se 2 (by rfl) ⟨553920, by rfl⟩ : syracuseStep 1477121 = 1107841) B1107841
theorem B985603 : Blo 984595 985603 := bstep (se 1 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 985603 = 1478405) B1478405
theorem B1477139 : Blo 984595 1477139 := bstep (se 1 (by rfl) ⟨1107854, by rfl⟩ : syracuseStep 1477139 = 2215709) B2215709
theorem B985619 : Blo 984595 985619 := bstep (se 1 (by rfl) ⟨739214, by rfl⟩ : syracuseStep 985619 = 1478429) B1478429
theorem B985635 : Blo 984595 985635 := bstep (se 1 (by rfl) ⟨739226, by rfl⟩ : syracuseStep 985635 = 1478453) B1478453
theorem B1477169 : Blo 984595 1477169 := bstep (se 2 (by rfl) ⟨553938, by rfl⟩ : syracuseStep 1477169 = 1107877) B1107877
theorem B2492977 : Blo 984595 2492977 := bstep (se 2 (by rfl) ⟨934866, by rfl⟩ : syracuseStep 2492977 = 1869733) B1869733
theorem B985651 : Blo 984595 985651 := bstep (se 1 (by rfl) ⟨739238, by rfl⟩ : syracuseStep 985651 = 1478477) B1478477
theorem B1477187 : Blo 984595 1477187 := bstep (se 1 (by rfl) ⟨1107890, by rfl⟩ : syracuseStep 1477187 = 2215781) B2215781
theorem B985667 : Blo 984595 985667 := bstep (se 1 (by rfl) ⟨739250, by rfl⟩ : syracuseStep 985667 = 1478501) B1478501
theorem B985683 : Blo 984595 985683 := bstep (se 1 (by rfl) ⟨739262, by rfl⟩ : syracuseStep 985683 = 1478525) B1478525
theorem B1477217 : Blo 984595 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B985699 : Blo 984595 985699 := bstep (se 1 (by rfl) ⟨739274, by rfl⟩ : syracuseStep 985699 = 1478549) B1478549
theorem B1477235 : Blo 984595 1477235 := bstep (se 1 (by rfl) ⟨1107926, by rfl⟩ : syracuseStep 1477235 = 2215853) B2215853
theorem B985715 : Blo 984595 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B985731 : Blo 984595 985731 := bstep (se 1 (by rfl) ⟨739298, by rfl⟩ : syracuseStep 985731 = 1478597) B1478597
theorem B1477265 : Blo 984595 1477265 := bstep (se 2 (by rfl) ⟨553974, by rfl⟩ : syracuseStep 1477265 = 1107949) B1107949
theorem B985747 : Blo 984595 985747 := bstep (se 1 (by rfl) ⟨739310, by rfl⟩ : syracuseStep 985747 = 1478621) B1478621
theorem B1477283 : Blo 984595 1477283 := bstep (se 1 (by rfl) ⟨1107962, by rfl⟩ : syracuseStep 1477283 = 2215925) B2215925
theorem B985763 : Blo 984595 985763 := bstep (se 1 (by rfl) ⟨739322, by rfl⟩ : syracuseStep 985763 = 1478645) B1478645
theorem B985779 : Blo 984595 985779 := bstep (se 1 (by rfl) ⟨739334, by rfl⟩ : syracuseStep 985779 = 1478669) B1478669
theorem B1477313 : Blo 984595 1477313 := bstep (se 2 (by rfl) ⟨553992, by rfl⟩ : syracuseStep 1477313 = 1107985) B1107985
theorem B985795 : Blo 984595 985795 := bstep (se 1 (by rfl) ⟨739346, by rfl⟩ : syracuseStep 985795 = 1478693) B1478693
theorem B1477331 : Blo 984595 1477331 := bstep (se 1 (by rfl) ⟨1107998, by rfl⟩ : syracuseStep 1477331 = 2215997) B2215997
theorem B985811 : Blo 984595 985811 := bstep (se 1 (by rfl) ⟨739358, by rfl⟩ : syracuseStep 985811 = 1478717) B1478717
theorem B985827 : Blo 984595 985827 := bstep (se 1 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 985827 = 1478741) B1478741
theorem B1477361 : Blo 984595 1477361 := bstep (se 2 (by rfl) ⟨554010, by rfl⟩ : syracuseStep 1477361 = 1108021) B1108021
theorem B5999345 : Blo 984595 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B985843 : Blo 984595 985843 := bstep (se 1 (by rfl) ⟨739382, by rfl⟩ : syracuseStep 985843 = 1478765) B1478765
theorem B1247987 : Blo 984595 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B1477379 : Blo 984595 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B985859 : Blo 984595 985859 := bstep (se 1 (by rfl) ⟨739394, by rfl⟩ : syracuseStep 985859 = 1478789) B1478789
theorem B985875 : Blo 984595 985875 := bstep (se 1 (by rfl) ⟨739406, by rfl⟩ : syracuseStep 985875 = 1478813) B1478813
theorem B1477409 : Blo 984595 1477409 := bstep (se 2 (by rfl) ⟨554028, by rfl⟩ : syracuseStep 1477409 = 1108057) B1108057
theorem B985891 : Blo 984595 985891 := bstep (se 1 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 985891 = 1478837) B1478837
theorem B1477427 : Blo 984595 1477427 := bstep (se 1 (by rfl) ⟨1108070, by rfl⟩ : syracuseStep 1477427 = 2216141) B2216141
theorem B985907 : Blo 984595 985907 := bstep (se 1 (by rfl) ⟨739430, by rfl⟩ : syracuseStep 985907 = 1478861) B1478861
theorem B2493251 : Blo 984595 2493251 := bstep (se 1 (by rfl) ⟨1869938, by rfl⟩ : syracuseStep 2493251 = 3739877) B3739877
theorem B985923 : Blo 984595 985923 := bstep (se 1 (by rfl) ⟨739442, by rfl⟩ : syracuseStep 985923 = 1478885) B1478885
theorem B1477457 : Blo 984595 1477457 := bstep (se 2 (by rfl) ⟨554046, by rfl⟩ : syracuseStep 1477457 = 1108093) B1108093
theorem B985939 : Blo 984595 985939 := bstep (se 1 (by rfl) ⟨739454, by rfl⟩ : syracuseStep 985939 = 1478909) B1478909
theorem B1477475 : Blo 984595 1477475 := bstep (se 1 (by rfl) ⟨1108106, by rfl⟩ : syracuseStep 1477475 = 2216213) B2216213
theorem B985955 : Blo 984595 985955 := bstep (se 1 (by rfl) ⟨739466, by rfl⟩ : syracuseStep 985955 = 1478933) B1478933
theorem B1870705 : Blo 984595 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B985971 : Blo 984595 985971 := bstep (se 1 (by rfl) ⟨739478, by rfl⟩ : syracuseStep 985971 = 1478957) B1478957
theorem B1477505 : Blo 984595 1477505 := bstep (se 2 (by rfl) ⟨554064, by rfl⟩ : syracuseStep 1477505 = 1108129) B1108129
theorem B985987 : Blo 984595 985987 := bstep (se 1 (by rfl) ⟨739490, by rfl⟩ : syracuseStep 985987 = 1478981) B1478981
theorem B1477523 : Blo 984595 1477523 := bstep (se 1 (by rfl) ⟨1108142, by rfl⟩ : syracuseStep 1477523 = 2216285) B2216285
theorem B986003 : Blo 984595 986003 := bstep (se 1 (by rfl) ⟨739502, by rfl⟩ : syracuseStep 986003 = 1479005) B1479005
theorem B986019 : Blo 984595 986019 := bstep (se 1 (by rfl) ⟨739514, by rfl⟩ : syracuseStep 986019 = 1479029) B1479029
theorem B2001827 : Blo 984595 2001827 := bstep (se 1 (by rfl) ⟨1501370, by rfl⟩ : syracuseStep 2001827 = 3002741) B3002741
theorem B1477553 : Blo 984595 1477553 := bstep (se 2 (by rfl) ⟨554082, by rfl⟩ : syracuseStep 1477553 = 1108165) B1108165
theorem B986035 : Blo 984595 986035 := bstep (se 1 (by rfl) ⟨739526, by rfl⟩ : syracuseStep 986035 = 1479053) B1479053
theorem B1477571 : Blo 984595 1477571 := bstep (se 1 (by rfl) ⟨1108178, by rfl⟩ : syracuseStep 1477571 = 2216357) B2216357
theorem B986051 : Blo 984595 986051 := bstep (se 1 (by rfl) ⟨739538, by rfl⟩ : syracuseStep 986051 = 1479077) B1479077
theorem B986067 : Blo 984595 986067 := bstep (se 1 (by rfl) ⟨739550, by rfl⟩ : syracuseStep 986067 = 1479101) B1479101
theorem B1477601 : Blo 984595 1477601 := bstep (se 2 (by rfl) ⟨554100, by rfl⟩ : syracuseStep 1477601 = 1108201) B1108201
theorem B986083 : Blo 984595 986083 := bstep (se 1 (by rfl) ⟨739562, by rfl⟩ : syracuseStep 986083 = 1479125) B1479125
theorem B1477619 : Blo 984595 1477619 := bstep (se 1 (by rfl) ⟨1108214, by rfl⟩ : syracuseStep 1477619 = 2216429) B2216429
theorem B986099 : Blo 984595 986099 := bstep (se 1 (by rfl) ⟨739574, by rfl⟩ : syracuseStep 986099 = 1479149) B1479149
theorem B2493443 : Blo 984595 2493443 := bstep (se 1 (by rfl) ⟨1870082, by rfl⟩ : syracuseStep 2493443 = 3740165) B3740165
theorem B986115 : Blo 984595 986115 := bstep (se 1 (by rfl) ⟨739586, by rfl⟩ : syracuseStep 986115 = 1479173) B1479173
theorem B1477649 : Blo 984595 1477649 := bstep (se 2 (by rfl) ⟨554118, by rfl⟩ : syracuseStep 1477649 = 1108237) B1108237
theorem B986131 : Blo 984595 986131 := bstep (se 1 (by rfl) ⟨739598, by rfl⟩ : syracuseStep 986131 = 1479197) B1479197
theorem B1477667 : Blo 984595 1477667 := bstep (se 1 (by rfl) ⟨1108250, by rfl⟩ : syracuseStep 1477667 = 2216501) B2216501
theorem B986147 : Blo 984595 986147 := bstep (se 1 (by rfl) ⟨739610, by rfl⟩ : syracuseStep 986147 = 1479221) B1479221
theorem B986163 : Blo 984595 986163 := bstep (se 1 (by rfl) ⟨739622, by rfl⟩ : syracuseStep 986163 = 1479245) B1479245
theorem B1477697 : Blo 984595 1477697 := bstep (se 2 (by rfl) ⟨554136, by rfl⟩ : syracuseStep 1477697 = 1108273) B1108273
theorem B986179 : Blo 984595 986179 := bstep (se 1 (by rfl) ⟨739634, by rfl⟩ : syracuseStep 986179 = 1479269) B1479269
theorem B1477715 : Blo 984595 1477715 := bstep (se 1 (by rfl) ⟨1108286, by rfl⟩ : syracuseStep 1477715 = 2216573) B2216573
theorem B986195 : Blo 984595 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B986211 : Blo 984595 986211 := bstep (se 1 (by rfl) ⟨739658, by rfl⟩ : syracuseStep 986211 = 1479317) B1479317
theorem B3738737 : Blo 984595 3738737 := bstep (se 2 (by rfl) ⟨1402026, by rfl⟩ : syracuseStep 3738737 = 2804053) B2804053
theorem B1477745 : Blo 984595 1477745 := bstep (se 2 (by rfl) ⟨554154, by rfl⟩ : syracuseStep 1477745 = 1108309) B1108309
theorem B986227 : Blo 984595 986227 := bstep (se 1 (by rfl) ⟨739670, by rfl⟩ : syracuseStep 986227 = 1479341) B1479341
theorem B1477763 : Blo 984595 1477763 := bstep (se 1 (by rfl) ⟨1108322, by rfl⟩ : syracuseStep 1477763 = 2216645) B2216645
theorem B986243 : Blo 984595 986243 := bstep (se 1 (by rfl) ⟨739682, by rfl⟩ : syracuseStep 986243 = 1479365) B1479365
theorem B11242637 : Blo 984595 11242637 := bstep (se 3 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 11242637 = 4215989) B4215989
theorem B986259 : Blo 984595 986259 := bstep (se 1 (by rfl) ⟨739694, by rfl⟩ : syracuseStep 986259 = 1479389) B1479389
theorem B1477793 : Blo 984595 1477793 := bstep (se 2 (by rfl) ⟨554172, by rfl⟩ : syracuseStep 1477793 = 1108345) B1108345
theorem B986275 : Blo 984595 986275 := bstep (se 1 (by rfl) ⟨739706, by rfl⟩ : syracuseStep 986275 = 1479413) B1479413
theorem B1477811 : Blo 984595 1477811 := bstep (se 1 (by rfl) ⟨1108358, by rfl⟩ : syracuseStep 1477811 = 2216717) B2216717
theorem B986291 : Blo 984595 986291 := bstep (se 1 (by rfl) ⟨739718, by rfl⟩ : syracuseStep 986291 = 1479437) B1479437
theorem B986307 : Blo 984595 986307 := bstep (se 1 (by rfl) ⟨739730, by rfl⟩ : syracuseStep 986307 = 1479461) B1479461
theorem B1477841 : Blo 984595 1477841 := bstep (se 2 (by rfl) ⟨554190, by rfl⟩ : syracuseStep 1477841 = 1108381) B1108381
theorem B986323 : Blo 984595 986323 := bstep (se 1 (by rfl) ⟨739742, by rfl⟩ : syracuseStep 986323 = 1479485) B1479485
theorem B1477859 : Blo 984595 1477859 := bstep (se 1 (by rfl) ⟨1108394, by rfl⟩ : syracuseStep 1477859 = 2216789) B2216789
theorem B986339 : Blo 984595 986339 := bstep (se 1 (by rfl) ⟨739754, by rfl⟩ : syracuseStep 986339 = 1479509) B1479509
theorem B986355 : Blo 984595 986355 := bstep (se 1 (by rfl) ⟨739766, by rfl⟩ : syracuseStep 986355 = 1479533) B1479533
theorem B1477889 : Blo 984595 1477889 := bstep (se 2 (by rfl) ⟨554208, by rfl⟩ : syracuseStep 1477889 = 1108417) B1108417
theorem B986371 : Blo 984595 986371 := bstep (se 1 (by rfl) ⟨739778, by rfl⟩ : syracuseStep 986371 = 1479557) B1479557
theorem B1477907 : Blo 984595 1477907 := bstep (se 1 (by rfl) ⟨1108430, by rfl⟩ : syracuseStep 1477907 = 2216861) B2216861
theorem B986387 : Blo 984595 986387 := bstep (se 1 (by rfl) ⟨739790, by rfl⟩ : syracuseStep 986387 = 1479581) B1479581
theorem B986403 : Blo 984595 986403 := bstep (se 1 (by rfl) ⟨739802, by rfl⟩ : syracuseStep 986403 = 1479605) B1479605
theorem B1477937 : Blo 984595 1477937 := bstep (se 2 (by rfl) ⟨554226, by rfl⟩ : syracuseStep 1477937 = 1108453) B1108453
theorem B986419 : Blo 984595 986419 := bstep (se 1 (by rfl) ⟨739814, by rfl⟩ : syracuseStep 986419 = 1479629) B1479629
theorem B1477955 : Blo 984595 1477955 := bstep (se 1 (by rfl) ⟨1108466, by rfl⟩ : syracuseStep 1477955 = 2216933) B2216933
theorem B986435 : Blo 984595 986435 := bstep (se 1 (by rfl) ⟨739826, by rfl⟩ : syracuseStep 986435 = 1479653) B1479653
theorem B986451 : Blo 984595 986451 := bstep (se 1 (by rfl) ⟨739838, by rfl⟩ : syracuseStep 986451 = 1479677) B1479677
theorem B1477985 : Blo 984595 1477985 := bstep (se 2 (by rfl) ⟨554244, by rfl⟩ : syracuseStep 1477985 = 1108489) B1108489
theorem B986467 : Blo 984595 986467 := bstep (se 1 (by rfl) ⟨739850, by rfl⟩ : syracuseStep 986467 = 1479701) B1479701
theorem B1478003 : Blo 984595 1478003 := bstep (se 1 (by rfl) ⟨1108502, by rfl⟩ : syracuseStep 1478003 = 2217005) B2217005
theorem B986483 : Blo 984595 986483 := bstep (se 1 (by rfl) ⟨739862, by rfl⟩ : syracuseStep 986483 = 1479725) B1479725
theorem B986499 : Blo 984595 986499 := bstep (se 1 (by rfl) ⟨739874, by rfl⟩ : syracuseStep 986499 = 1479749) B1479749
theorem B1478033 : Blo 984595 1478033 := bstep (se 2 (by rfl) ⟨554262, by rfl⟩ : syracuseStep 1478033 = 1108525) B1108525
theorem B986515 : Blo 984595 986515 := bstep (se 1 (by rfl) ⟨739886, by rfl⟩ : syracuseStep 986515 = 1479773) B1479773
theorem B1478051 : Blo 984595 1478051 := bstep (se 1 (by rfl) ⟨1108538, by rfl⟩ : syracuseStep 1478051 = 2217077) B2217077
theorem B986531 : Blo 984595 986531 := bstep (se 1 (by rfl) ⟨739898, by rfl⟩ : syracuseStep 986531 = 1479797) B1479797
theorem B986547 : Blo 984595 986547 := bstep (se 1 (by rfl) ⟨739910, by rfl⟩ : syracuseStep 986547 = 1479821) B1479821
theorem B1248691 : Blo 984595 1248691 := bstep (se 1 (by rfl) ⟨936518, by rfl⟩ : syracuseStep 1248691 = 1873037) B1873037
theorem B1478081 : Blo 984595 1478081 := bstep (se 2 (by rfl) ⟨554280, by rfl⟩ : syracuseStep 1478081 = 1108561) B1108561
theorem B986563 : Blo 984595 986563 := bstep (se 1 (by rfl) ⟨739922, by rfl⟩ : syracuseStep 986563 = 1479845) B1479845
theorem B7212485 : Blo 984595 7212485 := bstep (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) B1352341
theorem B1478099 : Blo 984595 1478099 := bstep (se 1 (by rfl) ⟨1108574, by rfl⟩ : syracuseStep 1478099 = 2217149) B2217149
theorem B986579 : Blo 984595 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B986595 : Blo 984595 986595 := bstep (se 1 (by rfl) ⟨739946, by rfl⟩ : syracuseStep 986595 = 1479893) B1479893
theorem B1478129 : Blo 984595 1478129 := bstep (se 2 (by rfl) ⟨554298, by rfl⟩ : syracuseStep 1478129 = 1108597) B1108597
theorem B986611 : Blo 984595 986611 := bstep (se 1 (by rfl) ⟨739958, by rfl⟩ : syracuseStep 986611 = 1479917) B1479917
theorem B1478147 : Blo 984595 1478147 := bstep (se 1 (by rfl) ⟨1108610, by rfl⟩ : syracuseStep 1478147 = 2217221) B2217221
theorem B986627 : Blo 984595 986627 := bstep (se 1 (by rfl) ⟨739970, by rfl⟩ : syracuseStep 986627 = 1479941) B1479941
theorem B986643 : Blo 984595 986643 := bstep (se 1 (by rfl) ⟨739982, by rfl⟩ : syracuseStep 986643 = 1479965) B1479965
theorem B1248787 : Blo 984595 1248787 := bstep (se 1 (by rfl) ⟨936590, by rfl⟩ : syracuseStep 1248787 = 1873181) B1873181
theorem B1478177 : Blo 984595 1478177 := bstep (se 2 (by rfl) ⟨554316, by rfl⟩ : syracuseStep 1478177 = 1108633) B1108633
theorem B1052195 : Blo 984595 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B986659 : Blo 984595 986659 := bstep (se 1 (by rfl) ⟨739994, by rfl⟩ : syracuseStep 986659 = 1479989) B1479989
theorem B1478195 : Blo 984595 1478195 := bstep (se 1 (by rfl) ⟨1108646, by rfl⟩ : syracuseStep 1478195 = 2217293) B2217293
theorem B986675 : Blo 984595 986675 := bstep (se 1 (by rfl) ⟨740006, by rfl⟩ : syracuseStep 986675 = 1480013) B1480013
theorem B986691 : Blo 984595 986691 := bstep (se 1 (by rfl) ⟨740018, by rfl⟩ : syracuseStep 986691 = 1480037) B1480037
theorem B1478225 : Blo 984595 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B986707 : Blo 984595 986707 := bstep (se 1 (by rfl) ⟨740030, by rfl⟩ : syracuseStep 986707 = 1480061) B1480061
theorem B1478243 : Blo 984595 1478243 := bstep (se 1 (by rfl) ⟨1108682, by rfl⟩ : syracuseStep 1478243 = 2217365) B2217365
theorem B986723 : Blo 984595 986723 := bstep (se 1 (by rfl) ⟨740042, by rfl⟩ : syracuseStep 986723 = 1480085) B1480085
theorem B986739 : Blo 984595 986739 := bstep (se 1 (by rfl) ⟨740054, by rfl⟩ : syracuseStep 986739 = 1480109) B1480109
theorem B1478273 : Blo 984595 1478273 := bstep (se 2 (by rfl) ⟨554352, by rfl⟩ : syracuseStep 1478273 = 1108705) B1108705
theorem B986755 : Blo 984595 986755 := bstep (se 1 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 986755 = 1480133) B1480133
theorem B1478291 : Blo 984595 1478291 := bstep (se 1 (by rfl) ⟨1108718, by rfl⟩ : syracuseStep 1478291 = 2217437) B2217437
theorem B986771 : Blo 984595 986771 := bstep (se 1 (by rfl) ⟨740078, by rfl⟩ : syracuseStep 986771 = 1480157) B1480157
theorem B986787 : Blo 984595 986787 := bstep (se 1 (by rfl) ⟨740090, by rfl⟩ : syracuseStep 986787 = 1480181) B1480181
theorem B1478321 : Blo 984595 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B986803 : Blo 984595 986803 := bstep (se 1 (by rfl) ⟨740102, by rfl⟩ : syracuseStep 986803 = 1480205) B1480205
theorem B1478339 : Blo 984595 1478339 := bstep (se 1 (by rfl) ⟨1108754, by rfl⟩ : syracuseStep 1478339 = 2217509) B2217509
theorem B986819 : Blo 984595 986819 := bstep (se 1 (by rfl) ⟨740114, by rfl⟩ : syracuseStep 986819 = 1480229) B1480229
theorem B986835 : Blo 984595 986835 := bstep (se 1 (by rfl) ⟨740126, by rfl⟩ : syracuseStep 986835 = 1480253) B1480253
theorem B1478369 : Blo 984595 1478369 := bstep (se 2 (by rfl) ⟨554388, by rfl⟩ : syracuseStep 1478369 = 1108777) B1108777
theorem B986851 : Blo 984595 986851 := bstep (se 1 (by rfl) ⟨740138, by rfl⟩ : syracuseStep 986851 = 1480277) B1480277
theorem B1478387 : Blo 984595 1478387 := bstep (se 1 (by rfl) ⟨1108790, by rfl⟩ : syracuseStep 1478387 = 2217581) B2217581
theorem B986867 : Blo 984595 986867 := bstep (se 1 (by rfl) ⟨740150, by rfl⟩ : syracuseStep 986867 = 1480301) B1480301
theorem B986883 : Blo 984595 986883 := bstep (se 1 (by rfl) ⟨740162, by rfl⟩ : syracuseStep 986883 = 1480325) B1480325
theorem B3739405 : Blo 984595 3739405 := bstep (se 3 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 3739405 = 1402277) B1402277
theorem B1478417 : Blo 984595 1478417 := bstep (se 2 (by rfl) ⟨554406, by rfl⟩ : syracuseStep 1478417 = 1108813) B1108813
theorem B986899 : Blo 984595 986899 := bstep (se 1 (by rfl) ⟨740174, by rfl⟩ : syracuseStep 986899 = 1480349) B1480349
theorem B1478435 : Blo 984595 1478435 := bstep (se 1 (by rfl) ⟨1108826, by rfl⟩ : syracuseStep 1478435 = 2217653) B2217653
theorem B986915 : Blo 984595 986915 := bstep (se 1 (by rfl) ⟨740186, by rfl⟩ : syracuseStep 986915 = 1480373) B1480373
theorem B986931 : Blo 984595 986931 := bstep (se 1 (by rfl) ⟨740198, by rfl⟩ : syracuseStep 986931 = 1480397) B1480397
theorem B1478465 : Blo 984595 1478465 := bstep (se 2 (by rfl) ⟨554424, by rfl⟩ : syracuseStep 1478465 = 1108849) B1108849
theorem B986947 : Blo 984595 986947 := bstep (se 1 (by rfl) ⟨740210, by rfl⟩ : syracuseStep 986947 = 1480421) B1480421
theorem B1478483 : Blo 984595 1478483 := bstep (se 1 (by rfl) ⟨1108862, by rfl⟩ : syracuseStep 1478483 = 2217725) B2217725
theorem B986963 : Blo 984595 986963 := bstep (se 1 (by rfl) ⟨740222, by rfl⟩ : syracuseStep 986963 = 1480445) B1480445
theorem B986979 : Blo 984595 986979 := bstep (se 1 (by rfl) ⟨740234, by rfl⟩ : syracuseStep 986979 = 1480469) B1480469
theorem B1478513 : Blo 984595 1478513 := bstep (se 2 (by rfl) ⟨554442, by rfl⟩ : syracuseStep 1478513 = 1108885) B1108885
theorem B986995 : Blo 984595 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B1478531 : Blo 984595 1478531 := bstep (se 1 (by rfl) ⟨1108898, by rfl⟩ : syracuseStep 1478531 = 2217797) B2217797
theorem B987011 : Blo 984595 987011 := bstep (se 1 (by rfl) ⟨740258, by rfl⟩ : syracuseStep 987011 = 1480517) B1480517
theorem B1871761 : Blo 984595 1871761 := bstep (se 2 (by rfl) ⟨701910, by rfl⟩ : syracuseStep 1871761 = 1403821) B1403821
theorem B987027 : Blo 984595 987027 := bstep (se 1 (by rfl) ⟨740270, by rfl⟩ : syracuseStep 987027 = 1480541) B1480541
theorem B1478561 : Blo 984595 1478561 := bstep (se 2 (by rfl) ⟨554460, by rfl⟩ : syracuseStep 1478561 = 1108921) B1108921
theorem B4984739 : Blo 984595 4984739 := bstep (se 1 (by rfl) ⟨3738554, by rfl⟩ : syracuseStep 4984739 = 7477109) B7477109
theorem B987043 : Blo 984595 987043 := bstep (se 1 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 987043 = 1480565) B1480565
theorem B2494385 : Blo 984595 2494385 := bstep (se 2 (by rfl) ⟨935394, by rfl⟩ : syracuseStep 2494385 = 1870789) B1870789
theorem B1478579 : Blo 984595 1478579 := bstep (se 1 (by rfl) ⟨1108934, by rfl⟩ : syracuseStep 1478579 = 2217869) B2217869
theorem B987059 : Blo 984595 987059 := bstep (se 1 (by rfl) ⟨740294, by rfl⟩ : syracuseStep 987059 = 1480589) B1480589
theorem B987075 : Blo 984595 987075 := bstep (se 1 (by rfl) ⟨740306, by rfl⟩ : syracuseStep 987075 = 1480613) B1480613
theorem B1478609 : Blo 984595 1478609 := bstep (se 2 (by rfl) ⟨554478, by rfl⟩ : syracuseStep 1478609 = 1108957) B1108957
theorem B987091 : Blo 984595 987091 := bstep (se 1 (by rfl) ⟨740318, by rfl⟩ : syracuseStep 987091 = 1480637) B1480637
theorem B2494435 : Blo 984595 2494435 := bstep (se 1 (by rfl) ⟨1870826, by rfl⟩ : syracuseStep 2494435 = 3741653) B3741653
theorem B1478627 : Blo 984595 1478627 := bstep (se 1 (by rfl) ⟨1108970, by rfl⟩ : syracuseStep 1478627 = 2217941) B2217941
theorem B987107 : Blo 984595 987107 := bstep (se 1 (by rfl) ⟨740330, by rfl⟩ : syracuseStep 987107 = 1480661) B1480661
theorem B987123 : Blo 984595 987123 := bstep (se 1 (by rfl) ⟨740342, by rfl⟩ : syracuseStep 987123 = 1480685) B1480685
theorem B1478657 : Blo 984595 1478657 := bstep (se 2 (by rfl) ⟨554496, by rfl⟩ : syracuseStep 1478657 = 1108993) B1108993
theorem B1249283 : Blo 984595 1249283 := bstep (se 1 (by rfl) ⟨936962, by rfl⟩ : syracuseStep 1249283 = 1873925) B1873925
theorem B987139 : Blo 984595 987139 := bstep (se 1 (by rfl) ⟨740354, by rfl⟩ : syracuseStep 987139 = 1480709) B1480709
theorem B1478675 : Blo 984595 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B987155 : Blo 984595 987155 := bstep (se 1 (by rfl) ⟨740366, by rfl⟩ : syracuseStep 987155 = 1480733) B1480733
theorem B987171 : Blo 984595 987171 := bstep (se 1 (by rfl) ⟨740378, by rfl⟩ : syracuseStep 987171 = 1480757) B1480757
theorem B1478705 : Blo 984595 1478705 := bstep (se 2 (by rfl) ⟨554514, by rfl⟩ : syracuseStep 1478705 = 1109029) B1109029
theorem B987187 : Blo 984595 987187 := bstep (se 1 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 987187 = 1480781) B1480781
theorem B1478723 : Blo 984595 1478723 := bstep (se 1 (by rfl) ⟨1109042, by rfl⟩ : syracuseStep 1478723 = 2218085) B2218085
theorem B987203 : Blo 984595 987203 := bstep (se 1 (by rfl) ⟨740402, by rfl⟩ : syracuseStep 987203 = 1480805) B1480805
theorem B987219 : Blo 984595 987219 := bstep (se 1 (by rfl) ⟨740414, by rfl⟩ : syracuseStep 987219 = 1480829) B1480829
theorem B1478753 : Blo 984595 1478753 := bstep (se 2 (by rfl) ⟨554532, by rfl⟩ : syracuseStep 1478753 = 1109065) B1109065
theorem B987235 : Blo 984595 987235 := bstep (se 1 (by rfl) ⟨740426, by rfl⟩ : syracuseStep 987235 = 1480853) B1480853
theorem B2494577 : Blo 984595 2494577 := bstep (se 2 (by rfl) ⟨935466, by rfl⟩ : syracuseStep 2494577 = 1870933) B1870933
theorem B1478771 : Blo 984595 1478771 := bstep (se 1 (by rfl) ⟨1109078, by rfl⟩ : syracuseStep 1478771 = 2218157) B2218157
theorem B987251 : Blo 984595 987251 := bstep (se 1 (by rfl) ⟨740438, by rfl⟩ : syracuseStep 987251 = 1480877) B1480877
theorem B987267 : Blo 984595 987267 := bstep (se 1 (by rfl) ⟨740450, by rfl⟩ : syracuseStep 987267 = 1480901) B1480901
theorem B12652685 : Blo 984595 12652685 := bstep (se 3 (by rfl) ⟨2372378, by rfl⟩ : syracuseStep 12652685 = 4744757) B4744757
theorem B1478801 : Blo 984595 1478801 := bstep (se 2 (by rfl) ⟨554550, by rfl⟩ : syracuseStep 1478801 = 1109101) B1109101
theorem B987283 : Blo 984595 987283 := bstep (se 1 (by rfl) ⟨740462, by rfl⟩ : syracuseStep 987283 = 1480925) B1480925
theorem B1478819 : Blo 984595 1478819 := bstep (se 1 (by rfl) ⟨1109114, by rfl⟩ : syracuseStep 1478819 = 2218229) B2218229
theorem B987299 : Blo 984595 987299 := bstep (se 1 (by rfl) ⟨740474, by rfl⟩ : syracuseStep 987299 = 1480949) B1480949
theorem B987315 : Blo 984595 987315 := bstep (se 1 (by rfl) ⟨740486, by rfl⟩ : syracuseStep 987315 = 1480973) B1480973
theorem B1478849 : Blo 984595 1478849 := bstep (se 2 (by rfl) ⟨554568, by rfl⟩ : syracuseStep 1478849 = 1109137) B1109137
theorem B987331 : Blo 984595 987331 := bstep (se 1 (by rfl) ⟨740498, by rfl⟩ : syracuseStep 987331 = 1480997) B1480997
theorem B5607629 : Blo 984595 5607629 := bstep (se 3 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 5607629 = 2102861) B2102861
theorem B1478867 : Blo 984595 1478867 := bstep (se 1 (by rfl) ⟨1109150, by rfl⟩ : syracuseStep 1478867 = 2218301) B2218301
theorem B987347 : Blo 984595 987347 := bstep (se 1 (by rfl) ⟨740510, by rfl⟩ : syracuseStep 987347 = 1481021) B1481021
theorem B987363 : Blo 984595 987363 := bstep (se 1 (by rfl) ⟨740522, by rfl⟩ : syracuseStep 987363 = 1481045) B1481045
theorem B1478897 : Blo 984595 1478897 := bstep (se 2 (by rfl) ⟨554586, by rfl⟩ : syracuseStep 1478897 = 1109173) B1109173
theorem B987379 : Blo 984595 987379 := bstep (se 1 (by rfl) ⟨740534, by rfl⟩ : syracuseStep 987379 = 1481069) B1481069
theorem B1478915 : Blo 984595 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B987395 : Blo 984595 987395 := bstep (se 1 (by rfl) ⟨740546, by rfl⟩ : syracuseStep 987395 = 1481093) B1481093
theorem B1052947 : Blo 984595 1052947 := bstep (se 1 (by rfl) ⟨789710, by rfl⟩ : syracuseStep 1052947 = 1579421) B1579421
theorem B987411 : Blo 984595 987411 := bstep (se 1 (by rfl) ⟨740558, by rfl⟩ : syracuseStep 987411 = 1481117) B1481117
theorem B1577249 : Blo 984595 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B1478945 : Blo 984595 1478945 := bstep (se 2 (by rfl) ⟨554604, by rfl⟩ : syracuseStep 1478945 = 1109209) B1109209
theorem B1872163 : Blo 984595 1872163 := bstep (se 1 (by rfl) ⟨1404122, by rfl⟩ : syracuseStep 1872163 = 2808245) B2808245
theorem B987427 : Blo 984595 987427 := bstep (se 1 (by rfl) ⟨740570, by rfl⟩ : syracuseStep 987427 = 1481141) B1481141
theorem B1478963 : Blo 984595 1478963 := bstep (se 1 (by rfl) ⟨1109222, by rfl⟩ : syracuseStep 1478963 = 2218445) B2218445
theorem B987443 : Blo 984595 987443 := bstep (se 1 (by rfl) ⟨740582, by rfl⟩ : syracuseStep 987443 = 1481165) B1481165
theorem B987459 : Blo 984595 987459 := bstep (se 1 (by rfl) ⟨740594, by rfl⟩ : syracuseStep 987459 = 1481189) B1481189
theorem B1478993 : Blo 984595 1478993 := bstep (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) B1109245
theorem B1872209 : Blo 984595 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B987475 : Blo 984595 987475 := bstep (se 1 (by rfl) ⟨740606, by rfl⟩ : syracuseStep 987475 = 1481213) B1481213
theorem B1479011 : Blo 984595 1479011 := bstep (se 1 (by rfl) ⟨1109258, by rfl⟩ : syracuseStep 1479011 = 2218517) B2218517
theorem B987491 : Blo 984595 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B987507 : Blo 984595 987507 := bstep (se 1 (by rfl) ⟨740630, by rfl⟩ : syracuseStep 987507 = 1481261) B1481261
theorem B1479041 : Blo 984595 1479041 := bstep (se 2 (by rfl) ⟨554640, by rfl⟩ : syracuseStep 1479041 = 1109281) B1109281
theorem B987523 : Blo 984595 987523 := bstep (se 1 (by rfl) ⟨740642, by rfl⟩ : syracuseStep 987523 = 1481285) B1481285
theorem B1479059 : Blo 984595 1479059 := bstep (se 1 (by rfl) ⟨1109294, by rfl⟩ : syracuseStep 1479059 = 2218589) B2218589
theorem B987539 : Blo 984595 987539 := bstep (se 1 (by rfl) ⟨740654, by rfl⟩ : syracuseStep 987539 = 1481309) B1481309
theorem B987555 : Blo 984595 987555 := bstep (se 1 (by rfl) ⟨740666, by rfl⟩ : syracuseStep 987555 = 1481333) B1481333
theorem B1479089 : Blo 984595 1479089 := bstep (se 2 (by rfl) ⟨554658, by rfl⟩ : syracuseStep 1479089 = 1109317) B1109317
theorem B987571 : Blo 984595 987571 := bstep (se 1 (by rfl) ⟨740678, by rfl⟩ : syracuseStep 987571 = 1481357) B1481357
theorem B1479107 : Blo 984595 1479107 := bstep (se 1 (by rfl) ⟨1109330, by rfl⟩ : syracuseStep 1479107 = 2218661) B2218661
theorem B987587 : Blo 984595 987587 := bstep (se 1 (by rfl) ⟨740690, by rfl⟩ : syracuseStep 987587 = 1481381) B1481381
theorem B8556997 : Blo 984595 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B987603 : Blo 984595 987603 := bstep (se 1 (by rfl) ⟨740702, by rfl⟩ : syracuseStep 987603 = 1481405) B1481405
theorem B1479137 : Blo 984595 1479137 := bstep (se 2 (by rfl) ⟨554676, by rfl⟩ : syracuseStep 1479137 = 1109353) B1109353
theorem B987619 : Blo 984595 987619 := bstep (se 1 (by rfl) ⟨740714, by rfl⟩ : syracuseStep 987619 = 1481429) B1481429
theorem B1479155 : Blo 984595 1479155 := bstep (se 1 (by rfl) ⟨1109366, by rfl⟩ : syracuseStep 1479155 = 2218733) B2218733
theorem B987635 : Blo 984595 987635 := bstep (se 1 (by rfl) ⟨740726, by rfl⟩ : syracuseStep 987635 = 1481453) B1481453
theorem B987651 : Blo 984595 987651 := bstep (se 1 (by rfl) ⟨740738, by rfl⟩ : syracuseStep 987651 = 1481477) B1481477
theorem B1479185 : Blo 984595 1479185 := bstep (se 2 (by rfl) ⟨554694, by rfl⟩ : syracuseStep 1479185 = 1109389) B1109389
theorem B987667 : Blo 984595 987667 := bstep (se 1 (by rfl) ⟨740750, by rfl⟩ : syracuseStep 987667 = 1481501) B1481501
theorem B3740195 : Blo 984595 3740195 := bstep (se 1 (by rfl) ⟨2805146, by rfl⟩ : syracuseStep 3740195 = 5610293) B5610293
theorem B1479203 : Blo 984595 1479203 := bstep (se 1 (by rfl) ⟨1109402, by rfl⟩ : syracuseStep 1479203 = 2218805) B2218805
theorem B987683 : Blo 984595 987683 := bstep (se 1 (by rfl) ⟨740762, by rfl⟩ : syracuseStep 987683 = 1481525) B1481525
theorem B987699 : Blo 984595 987699 := bstep (se 1 (by rfl) ⟨740774, by rfl⟩ : syracuseStep 987699 = 1481549) B1481549
theorem B1479233 : Blo 984595 1479233 := bstep (se 2 (by rfl) ⟨554712, by rfl⟩ : syracuseStep 1479233 = 1109425) B1109425
theorem B987715 : Blo 984595 987715 := bstep (se 1 (by rfl) ⟨740786, by rfl⟩ : syracuseStep 987715 = 1481573) B1481573
theorem B1479251 : Blo 984595 1479251 := bstep (se 1 (by rfl) ⟨1109438, by rfl⟩ : syracuseStep 1479251 = 2218877) B2218877
theorem B987731 : Blo 984595 987731 := bstep (se 1 (by rfl) ⟨740798, by rfl⟩ : syracuseStep 987731 = 1481597) B1481597
theorem B987747 : Blo 984595 987747 := bstep (se 1 (by rfl) ⟨740810, by rfl⟩ : syracuseStep 987747 = 1481621) B1481621
theorem B1479281 : Blo 984595 1479281 := bstep (se 2 (by rfl) ⟨554730, by rfl⟩ : syracuseStep 1479281 = 1109461) B1109461
theorem B1872497 : Blo 984595 1872497 := bstep (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) B1404373
theorem B987763 : Blo 984595 987763 := bstep (se 1 (by rfl) ⟨740822, by rfl⟩ : syracuseStep 987763 = 1481645) B1481645
theorem B1479299 : Blo 984595 1479299 := bstep (se 1 (by rfl) ⟨1109474, by rfl⟩ : syracuseStep 1479299 = 2218949) B2218949
theorem B987779 : Blo 984595 987779 := bstep (se 1 (by rfl) ⟨740834, by rfl⟩ : syracuseStep 987779 = 1481669) B1481669
theorem B23368333 : Blo 984595 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B987795 : Blo 984595 987795 := bstep (se 1 (by rfl) ⟨740846, by rfl⟩ : syracuseStep 987795 = 1481693) B1481693
theorem B1479329 : Blo 984595 1479329 := bstep (se 2 (by rfl) ⟨554748, by rfl⟩ : syracuseStep 1479329 = 1109497) B1109497
theorem B987811 : Blo 984595 987811 := bstep (se 1 (by rfl) ⟨740858, by rfl⟩ : syracuseStep 987811 = 1481717) B1481717
theorem B1479347 : Blo 984595 1479347 := bstep (se 1 (by rfl) ⟨1109510, by rfl⟩ : syracuseStep 1479347 = 2219021) B2219021
theorem B987827 : Blo 984595 987827 := bstep (se 1 (by rfl) ⟨740870, by rfl⟩ : syracuseStep 987827 = 1481741) B1481741
theorem B1249987 : Blo 984595 1249987 := bstep (se 1 (by rfl) ⟨937490, by rfl⟩ : syracuseStep 1249987 = 1874981) B1874981
theorem B987843 : Blo 984595 987843 := bstep (se 1 (by rfl) ⟨740882, by rfl⟩ : syracuseStep 987843 = 1481765) B1481765
theorem B4985549 : Blo 984595 4985549 := bstep (se 3 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 4985549 = 1869581) B1869581
theorem B1479377 : Blo 984595 1479377 := bstep (se 2 (by rfl) ⟨554766, by rfl⟩ : syracuseStep 1479377 = 1109533) B1109533
theorem B987859 : Blo 984595 987859 := bstep (se 1 (by rfl) ⟨740894, by rfl⟩ : syracuseStep 987859 = 1481789) B1481789
theorem B1479395 : Blo 984595 1479395 := bstep (se 1 (by rfl) ⟨1109546, by rfl⟩ : syracuseStep 1479395 = 2219093) B2219093
theorem B987875 : Blo 984595 987875 := bstep (se 1 (by rfl) ⟨740906, by rfl⟩ : syracuseStep 987875 = 1481813) B1481813
theorem B987891 : Blo 984595 987891 := bstep (se 1 (by rfl) ⟨740918, by rfl⟩ : syracuseStep 987891 = 1481837) B1481837
theorem B1479425 : Blo 984595 1479425 := bstep (se 2 (by rfl) ⟨554784, by rfl⟩ : syracuseStep 1479425 = 1109569) B1109569
theorem B987907 : Blo 984595 987907 := bstep (se 1 (by rfl) ⟨740930, by rfl⟩ : syracuseStep 987907 = 1481861) B1481861
theorem B1479443 : Blo 984595 1479443 := bstep (se 1 (by rfl) ⟨1109582, by rfl⟩ : syracuseStep 1479443 = 2219165) B2219165
theorem B987923 : Blo 984595 987923 := bstep (se 1 (by rfl) ⟨740942, by rfl⟩ : syracuseStep 987923 = 1481885) B1481885
theorem B1250083 : Blo 984595 1250083 := bstep (se 1 (by rfl) ⟨937562, by rfl⟩ : syracuseStep 1250083 = 1875125) B1875125
theorem B987939 : Blo 984595 987939 := bstep (se 1 (by rfl) ⟨740954, by rfl⟩ : syracuseStep 987939 = 1481909) B1481909
theorem B1479473 : Blo 984595 1479473 := bstep (se 2 (by rfl) ⟨554802, by rfl⟩ : syracuseStep 1479473 = 1109605) B1109605
theorem B987955 : Blo 984595 987955 := bstep (se 1 (by rfl) ⟨740966, by rfl⟩ : syracuseStep 987955 = 1481933) B1481933
theorem B10654517 : Blo 984595 10654517 := bstep (se 5 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 10654517 = 998861) B998861
theorem B1479491 : Blo 984595 1479491 := bstep (se 1 (by rfl) ⟨1109618, by rfl⟩ : syracuseStep 1479491 = 2219237) B2219237
theorem B987971 : Blo 984595 987971 := bstep (se 1 (by rfl) ⟨740978, by rfl⟩ : syracuseStep 987971 = 1481957) B1481957
theorem B987987 : Blo 984595 987987 := bstep (se 1 (by rfl) ⟨740990, by rfl⟩ : syracuseStep 987987 = 1481981) B1481981
theorem B1479521 : Blo 984595 1479521 := bstep (se 2 (by rfl) ⟨554820, by rfl⟩ : syracuseStep 1479521 = 1109641) B1109641
theorem B988003 : Blo 984595 988003 := bstep (se 1 (by rfl) ⟨741002, by rfl⟩ : syracuseStep 988003 = 1482005) B1482005
theorem B1479539 : Blo 984595 1479539 := bstep (se 1 (by rfl) ⟨1109654, by rfl⟩ : syracuseStep 1479539 = 2219309) B2219309
theorem B988019 : Blo 984595 988019 := bstep (se 1 (by rfl) ⟨741014, by rfl⟩ : syracuseStep 988019 = 1482029) B1482029
theorem B988035 : Blo 984595 988035 := bstep (se 1 (by rfl) ⟨741026, by rfl⟩ : syracuseStep 988035 = 1482053) B1482053
theorem B1479569 : Blo 984595 1479569 := bstep (se 2 (by rfl) ⟨554838, by rfl⟩ : syracuseStep 1479569 = 1109677) B1109677
theorem B988051 : Blo 984595 988051 := bstep (se 1 (by rfl) ⟨741038, by rfl⟩ : syracuseStep 988051 = 1482077) B1482077
theorem B1479587 : Blo 984595 1479587 := bstep (se 1 (by rfl) ⟨1109690, by rfl⟩ : syracuseStep 1479587 = 2219381) B2219381
theorem B988067 : Blo 984595 988067 := bstep (se 1 (by rfl) ⟨741050, by rfl⟩ : syracuseStep 988067 = 1482101) B1482101
theorem B988083 : Blo 984595 988083 := bstep (se 1 (by rfl) ⟨741062, by rfl⟩ : syracuseStep 988083 = 1482125) B1482125
theorem B1479617 : Blo 984595 1479617 := bstep (se 2 (by rfl) ⟨554856, by rfl⟩ : syracuseStep 1479617 = 1109713) B1109713
theorem B988099 : Blo 984595 988099 := bstep (se 1 (by rfl) ⟨741074, by rfl⟩ : syracuseStep 988099 = 1482149) B1482149
theorem B1479635 : Blo 984595 1479635 := bstep (se 1 (by rfl) ⟨1109726, by rfl⟩ : syracuseStep 1479635 = 2219453) B2219453
theorem B988115 : Blo 984595 988115 := bstep (se 1 (by rfl) ⟨741086, by rfl⟩ : syracuseStep 988115 = 1482173) B1482173
theorem B6329315 : Blo 984595 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B988131 : Blo 984595 988131 := bstep (se 1 (by rfl) ⟨741098, by rfl⟩ : syracuseStep 988131 = 1482197) B1482197
theorem B1479665 : Blo 984595 1479665 := bstep (se 2 (by rfl) ⟨554874, by rfl⟩ : syracuseStep 1479665 = 1109749) B1109749
theorem B988147 : Blo 984595 988147 := bstep (se 1 (by rfl) ⟨741110, by rfl⟩ : syracuseStep 988147 = 1482221) B1482221
theorem B1479683 : Blo 984595 1479683 := bstep (se 1 (by rfl) ⟨1109762, by rfl⟩ : syracuseStep 1479683 = 2219525) B2219525
theorem B988163 : Blo 984595 988163 := bstep (se 1 (by rfl) ⟨741122, by rfl⟩ : syracuseStep 988163 = 1482245) B1482245
theorem B988179 : Blo 984595 988179 := bstep (se 1 (by rfl) ⟨741134, by rfl⟩ : syracuseStep 988179 = 1482269) B1482269
theorem B1479713 : Blo 984595 1479713 := bstep (se 2 (by rfl) ⟨554892, by rfl⟩ : syracuseStep 1479713 = 1109785) B1109785
theorem B988195 : Blo 984595 988195 := bstep (se 1 (by rfl) ⟨741146, by rfl⟩ : syracuseStep 988195 = 1482293) B1482293
theorem B1479731 : Blo 984595 1479731 := bstep (se 1 (by rfl) ⟨1109798, by rfl⟩ : syracuseStep 1479731 = 2219597) B2219597
theorem B988211 : Blo 984595 988211 := bstep (se 1 (by rfl) ⟨741158, by rfl⟩ : syracuseStep 988211 = 1482317) B1482317
theorem B988227 : Blo 984595 988227 := bstep (se 1 (by rfl) ⟨741170, by rfl⟩ : syracuseStep 988227 = 1482341) B1482341
theorem B2495569 : Blo 984595 2495569 := bstep (se 2 (by rfl) ⟨935838, by rfl⟩ : syracuseStep 2495569 = 1871677) B1871677
theorem B1479761 : Blo 984595 1479761 := bstep (se 2 (by rfl) ⟨554910, by rfl⟩ : syracuseStep 1479761 = 1109821) B1109821
theorem B988243 : Blo 984595 988243 := bstep (se 1 (by rfl) ⟨741182, by rfl⟩ : syracuseStep 988243 = 1482365) B1482365
theorem B1479779 : Blo 984595 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B988259 : Blo 984595 988259 := bstep (se 1 (by rfl) ⟨741194, by rfl⟩ : syracuseStep 988259 = 1482389) B1482389
theorem B5608561 : Blo 984595 5608561 := bstep (se 2 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 5608561 = 4206421) B4206421
theorem B988275 : Blo 984595 988275 := bstep (se 1 (by rfl) ⟨741206, by rfl⟩ : syracuseStep 988275 = 1482413) B1482413
theorem B1479809 : Blo 984595 1479809 := bstep (se 2 (by rfl) ⟨554928, by rfl⟩ : syracuseStep 1479809 = 1109857) B1109857
theorem B988291 : Blo 984595 988291 := bstep (se 1 (by rfl) ⟨741218, by rfl⟩ : syracuseStep 988291 = 1482437) B1482437
theorem B1479827 : Blo 984595 1479827 := bstep (se 1 (by rfl) ⟨1109870, by rfl⟩ : syracuseStep 1479827 = 2219741) B2219741
theorem B988307 : Blo 984595 988307 := bstep (se 1 (by rfl) ⟨741230, by rfl⟩ : syracuseStep 988307 = 1482461) B1482461
theorem B988323 : Blo 984595 988323 := bstep (se 1 (by rfl) ⟨741242, by rfl⟩ : syracuseStep 988323 = 1482485) B1482485
theorem B3740849 : Blo 984595 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1479857 : Blo 984595 1479857 := bstep (se 2 (by rfl) ⟨554946, by rfl⟩ : syracuseStep 1479857 = 1109893) B1109893
theorem B988339 : Blo 984595 988339 := bstep (se 1 (by rfl) ⟨741254, by rfl⟩ : syracuseStep 988339 = 1482509) B1482509
theorem B1479875 : Blo 984595 1479875 := bstep (se 1 (by rfl) ⟨1109906, by rfl⟩ : syracuseStep 1479875 = 2219813) B2219813
theorem B988355 : Blo 984595 988355 := bstep (se 1 (by rfl) ⟨741266, by rfl⟩ : syracuseStep 988355 = 1482533) B1482533
theorem B988371 : Blo 984595 988371 := bstep (se 1 (by rfl) ⟨741278, by rfl⟩ : syracuseStep 988371 = 1482557) B1482557
theorem B1479905 : Blo 984595 1479905 := bstep (se 2 (by rfl) ⟨554964, by rfl⟩ : syracuseStep 1479905 = 1109929) B1109929
theorem B988387 : Blo 984595 988387 := bstep (se 1 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 988387 = 1482581) B1482581
theorem B1479923 : Blo 984595 1479923 := bstep (se 1 (by rfl) ⟨1109942, by rfl⟩ : syracuseStep 1479923 = 2219885) B2219885
theorem B988403 : Blo 984595 988403 := bstep (se 1 (by rfl) ⟨741302, by rfl⟩ : syracuseStep 988403 = 1482605) B1482605
theorem B988419 : Blo 984595 988419 := bstep (se 1 (by rfl) ⟨741314, by rfl⟩ : syracuseStep 988419 = 1482629) B1482629
theorem B1479953 : Blo 984595 1479953 := bstep (se 2 (by rfl) ⟨554982, by rfl⟩ : syracuseStep 1479953 = 1109965) B1109965
theorem B1250579 : Blo 984595 1250579 := bstep (se 1 (by rfl) ⟨937934, by rfl⟩ : syracuseStep 1250579 = 1875869) B1875869
theorem B988435 : Blo 984595 988435 := bstep (se 1 (by rfl) ⟨741326, by rfl⟩ : syracuseStep 988435 = 1482653) B1482653
theorem B1479971 : Blo 984595 1479971 := bstep (se 1 (by rfl) ⟨1109978, by rfl⟩ : syracuseStep 1479971 = 2219957) B2219957
theorem B988451 : Blo 984595 988451 := bstep (se 1 (by rfl) ⟨741338, by rfl⟩ : syracuseStep 988451 = 1482677) B1482677
theorem B988467 : Blo 984595 988467 := bstep (se 1 (by rfl) ⟨741350, by rfl⟩ : syracuseStep 988467 = 1482701) B1482701
theorem B1480001 : Blo 984595 1480001 := bstep (se 2 (by rfl) ⟨555000, by rfl⟩ : syracuseStep 1480001 = 1110001) B1110001
theorem B1873219 : Blo 984595 1873219 := bstep (se 1 (by rfl) ⟨1404914, by rfl⟩ : syracuseStep 1873219 = 2809829) B2809829
theorem B988483 : Blo 984595 988483 := bstep (se 1 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 988483 = 1482725) B1482725
theorem B1480019 : Blo 984595 1480019 := bstep (se 1 (by rfl) ⟨1110014, by rfl⟩ : syracuseStep 1480019 = 2220029) B2220029
theorem B988499 : Blo 984595 988499 := bstep (se 1 (by rfl) ⟨741374, by rfl⟩ : syracuseStep 988499 = 1482749) B1482749
theorem B2495843 : Blo 984595 2495843 := bstep (se 1 (by rfl) ⟨1871882, by rfl⟩ : syracuseStep 2495843 = 3743765) B3743765
theorem B988515 : Blo 984595 988515 := bstep (se 1 (by rfl) ⟨741386, by rfl⟩ : syracuseStep 988515 = 1482773) B1482773
theorem B1480049 : Blo 984595 1480049 := bstep (se 2 (by rfl) ⟨555018, by rfl⟩ : syracuseStep 1480049 = 1110037) B1110037
theorem B988531 : Blo 984595 988531 := bstep (se 1 (by rfl) ⟨741398, by rfl⟩ : syracuseStep 988531 = 1482797) B1482797
theorem B1480067 : Blo 984595 1480067 := bstep (se 1 (by rfl) ⟨1110050, by rfl⟩ : syracuseStep 1480067 = 2220101) B2220101
theorem B988547 : Blo 984595 988547 := bstep (se 1 (by rfl) ⟨741410, by rfl⟩ : syracuseStep 988547 = 1482821) B1482821
theorem B988563 : Blo 984595 988563 := bstep (se 1 (by rfl) ⟨741422, by rfl⟩ : syracuseStep 988563 = 1482845) B1482845
theorem B1480097 : Blo 984595 1480097 := bstep (se 2 (by rfl) ⟨555036, by rfl⟩ : syracuseStep 1480097 = 1110073) B1110073
theorem B988579 : Blo 984595 988579 := bstep (se 1 (by rfl) ⟨741434, by rfl⟩ : syracuseStep 988579 = 1482869) B1482869
theorem B1480115 : Blo 984595 1480115 := bstep (se 1 (by rfl) ⟨1110086, by rfl⟩ : syracuseStep 1480115 = 2220173) B2220173
theorem B988595 : Blo 984595 988595 := bstep (se 1 (by rfl) ⟨741446, by rfl⟩ : syracuseStep 988595 = 1482893) B1482893
theorem B1480145 : Blo 984595 1480145 := bstep (se 2 (by rfl) ⟨555054, by rfl⟩ : syracuseStep 1480145 = 1110109) B1110109
theorem B1480163 : Blo 984595 1480163 := bstep (se 1 (by rfl) ⟨1110122, by rfl⟩ : syracuseStep 1480163 = 2220245) B2220245
theorem B1480193 : Blo 984595 1480193 := bstep (se 2 (by rfl) ⟨555072, by rfl⟩ : syracuseStep 1480193 = 1110145) B1110145
theorem B1480211 : Blo 984595 1480211 := bstep (se 1 (by rfl) ⟨1110158, by rfl⟩ : syracuseStep 1480211 = 2220317) B2220317
theorem B2496035 : Blo 984595 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1480241 : Blo 984595 1480241 := bstep (se 2 (by rfl) ⟨555090, by rfl⟩ : syracuseStep 1480241 = 1110181) B1110181
theorem B1480259 : Blo 984595 1480259 := bstep (se 1 (by rfl) ⟨1110194, by rfl⟩ : syracuseStep 1480259 = 2220389) B2220389
theorem B1480289 : Blo 984595 1480289 := bstep (se 2 (by rfl) ⟨555108, by rfl⟩ : syracuseStep 1480289 = 1110217) B1110217
theorem B18257521 : Blo 984595 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B1480307 : Blo 984595 1480307 := bstep (se 1 (by rfl) ⟨1110230, by rfl⟩ : syracuseStep 1480307 = 2220461) B2220461
theorem B1054339 : Blo 984595 1054339 := bstep (se 1 (by rfl) ⟨790754, by rfl⟩ : syracuseStep 1054339 = 1581509) B1581509
theorem B1480337 : Blo 984595 1480337 := bstep (se 2 (by rfl) ⟨555126, by rfl⟩ : syracuseStep 1480337 = 1110253) B1110253
theorem B1480355 : Blo 984595 1480355 := bstep (se 1 (by rfl) ⟨1110266, by rfl⟩ : syracuseStep 1480355 = 2220533) B2220533
theorem B1480385 : Blo 984595 1480385 := bstep (se 2 (by rfl) ⟨555144, by rfl⟩ : syracuseStep 1480385 = 1110289) B1110289
theorem B1480403 : Blo 984595 1480403 := bstep (se 1 (by rfl) ⟨1110302, by rfl⟩ : syracuseStep 1480403 = 2220605) B2220605
theorem B1480433 : Blo 984595 1480433 := bstep (se 2 (by rfl) ⟨555162, by rfl⟩ : syracuseStep 1480433 = 1110325) B1110325
theorem B1775363 : Blo 984595 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B1873667 : Blo 984595 1873667 := bstep (se 1 (by rfl) ⟨1405250, by rfl⟩ : syracuseStep 1873667 = 2810501) B2810501
theorem B1480451 : Blo 984595 1480451 := bstep (se 1 (by rfl) ⟨1110338, by rfl⟩ : syracuseStep 1480451 = 2220677) B2220677
theorem B1480481 : Blo 984595 1480481 := bstep (se 2 (by rfl) ⟨555180, by rfl⟩ : syracuseStep 1480481 = 1110361) B1110361
theorem B1480499 : Blo 984595 1480499 := bstep (se 1 (by rfl) ⟨1110374, by rfl⟩ : syracuseStep 1480499 = 2220749) B2220749
theorem B1480529 : Blo 984595 1480529 := bstep (se 2 (by rfl) ⟨555198, by rfl⟩ : syracuseStep 1480529 = 1110397) B1110397
theorem B1480547 : Blo 984595 1480547 := bstep (se 1 (by rfl) ⟨1110410, by rfl⟩ : syracuseStep 1480547 = 2220821) B2220821
theorem B1480577 : Blo 984595 1480577 := bstep (se 2 (by rfl) ⟨555216, by rfl⟩ : syracuseStep 1480577 = 1110433) B1110433
theorem B1480595 : Blo 984595 1480595 := bstep (se 1 (by rfl) ⟨1110446, by rfl⟩ : syracuseStep 1480595 = 2220893) B2220893
theorem B1775537 : Blo 984595 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1480625 : Blo 984595 1480625 := bstep (se 2 (by rfl) ⟨555234, by rfl⟩ : syracuseStep 1480625 = 1110469) B1110469
theorem B1480643 : Blo 984595 1480643 := bstep (se 1 (by rfl) ⟨1110482, by rfl⟩ : syracuseStep 1480643 = 2220965) B2220965
theorem B11999173 : Blo 984595 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B1480673 : Blo 984595 1480673 := bstep (se 2 (by rfl) ⟨555252, by rfl⟩ : syracuseStep 1480673 = 1110505) B1110505
theorem B11245553 : Blo 984595 11245553 := bstep (se 2 (by rfl) ⟨4217082, by rfl⟩ : syracuseStep 11245553 = 8434165) B8434165
theorem B1480691 : Blo 984595 1480691 := bstep (se 1 (by rfl) ⟨1110518, by rfl⟩ : syracuseStep 1480691 = 2221037) B2221037
theorem B1480721 : Blo 984595 1480721 := bstep (se 2 (by rfl) ⟨555270, by rfl⟩ : syracuseStep 1480721 = 1110541) B1110541
theorem B1873955 : Blo 984595 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B1480739 : Blo 984595 1480739 := bstep (se 1 (by rfl) ⟨1110554, by rfl⟩ : syracuseStep 1480739 = 2221109) B2221109
theorem B1480769 : Blo 984595 1480769 := bstep (se 2 (by rfl) ⟨555288, by rfl⟩ : syracuseStep 1480769 = 1110577) B1110577
theorem B1480787 : Blo 984595 1480787 := bstep (se 1 (by rfl) ⟨1110590, by rfl⟩ : syracuseStep 1480787 = 2221181) B2221181
theorem B1480817 : Blo 984595 1480817 := bstep (se 2 (by rfl) ⟨555306, by rfl⟩ : syracuseStep 1480817 = 1110613) B1110613
theorem B1480835 : Blo 984595 1480835 := bstep (se 1 (by rfl) ⟨1110626, by rfl⟩ : syracuseStep 1480835 = 2221253) B2221253
theorem B1480865 : Blo 984595 1480865 := bstep (se 2 (by rfl) ⟨555324, by rfl⟩ : syracuseStep 1480865 = 1110649) B1110649
theorem B6330545 : Blo 984595 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B1480883 : Blo 984595 1480883 := bstep (se 1 (by rfl) ⟨1110662, by rfl⟩ : syracuseStep 1480883 = 2221325) B2221325
theorem B1480913 : Blo 984595 1480913 := bstep (se 2 (by rfl) ⟨555342, by rfl⟩ : syracuseStep 1480913 = 1110685) B1110685
theorem B1480931 : Blo 984595 1480931 := bstep (se 1 (by rfl) ⟨1110698, by rfl⟩ : syracuseStep 1480931 = 2221397) B2221397
theorem B1480961 : Blo 984595 1480961 := bstep (se 2 (by rfl) ⟨555360, by rfl⟩ : syracuseStep 1480961 = 1110721) B1110721
theorem B1579267 : Blo 984595 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B1480979 : Blo 984595 1480979 := bstep (se 1 (by rfl) ⟨1110734, by rfl⟩ : syracuseStep 1480979 = 2221469) B2221469
theorem B2103587 : Blo 984595 2103587 := bstep (se 1 (by rfl) ⟨1577690, by rfl⟩ : syracuseStep 2103587 = 3155381) B3155381
theorem B1481009 : Blo 984595 1481009 := bstep (se 2 (by rfl) ⟨555378, by rfl⟩ : syracuseStep 1481009 = 1110757) B1110757
theorem B1579331 : Blo 984595 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B1481027 : Blo 984595 1481027 := bstep (se 1 (by rfl) ⟨1110770, by rfl⟩ : syracuseStep 1481027 = 2221541) B2221541
theorem B1481057 : Blo 984595 1481057 := bstep (se 2 (by rfl) ⟨555396, by rfl⟩ : syracuseStep 1481057 = 1110793) B1110793
theorem B1481075 : Blo 984595 1481075 := bstep (se 1 (by rfl) ⟨1110806, by rfl⟩ : syracuseStep 1481075 = 2221613) B2221613
theorem B1481105 : Blo 984595 1481105 := bstep (se 2 (by rfl) ⟨555414, by rfl⟩ : syracuseStep 1481105 = 1110829) B1110829
theorem B1481123 : Blo 984595 1481123 := bstep (se 1 (by rfl) ⟨1110842, by rfl⟩ : syracuseStep 1481123 = 2221685) B2221685
theorem B1481153 : Blo 984595 1481153 := bstep (se 2 (by rfl) ⟨555432, by rfl⟩ : syracuseStep 1481153 = 1110865) B1110865
theorem B2496977 : Blo 984595 2496977 := bstep (se 2 (by rfl) ⟨936366, by rfl⟩ : syracuseStep 2496977 = 1872733) B1872733
theorem B1481171 : Blo 984595 1481171 := bstep (se 1 (by rfl) ⟨1110878, by rfl⟩ : syracuseStep 1481171 = 2221757) B2221757
theorem B1481201 : Blo 984595 1481201 := bstep (se 2 (by rfl) ⟨555450, by rfl⟩ : syracuseStep 1481201 = 1110901) B1110901
theorem B2497027 : Blo 984595 2497027 := bstep (se 1 (by rfl) ⟨1872770, by rfl⟩ : syracuseStep 2497027 = 3745541) B3745541
theorem B1481219 : Blo 984595 1481219 := bstep (se 1 (by rfl) ⟨1110914, by rfl⟩ : syracuseStep 1481219 = 2221829) B2221829
theorem B1481249 : Blo 984595 1481249 := bstep (se 2 (by rfl) ⟨555468, by rfl⟩ : syracuseStep 1481249 = 1110937) B1110937
theorem B5610019 : Blo 984595 5610019 := bstep (se 1 (by rfl) ⟨4207514, by rfl⟩ : syracuseStep 5610019 = 8415029) B8415029
theorem B1481267 : Blo 984595 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B1481297 : Blo 984595 1481297 := bstep (se 2 (by rfl) ⟨555486, by rfl⟩ : syracuseStep 1481297 = 1110973) B1110973
theorem B3742307 : Blo 984595 3742307 := bstep (se 1 (by rfl) ⟨2806730, by rfl⟩ : syracuseStep 3742307 = 5613461) B5613461
theorem B1481315 : Blo 984595 1481315 := bstep (se 1 (by rfl) ⟨1110986, by rfl⟩ : syracuseStep 1481315 = 2221973) B2221973
theorem B3742321 : Blo 984595 3742321 := bstep (se 2 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 3742321 = 2806741) B2806741
theorem B1481345 : Blo 984595 1481345 := bstep (se 2 (by rfl) ⟨555504, by rfl⟩ : syracuseStep 1481345 = 1111009) B1111009
theorem B2497169 : Blo 984595 2497169 := bstep (se 2 (by rfl) ⟨936438, by rfl⟩ : syracuseStep 2497169 = 1872877) B1872877
theorem B1481363 : Blo 984595 1481363 := bstep (se 1 (by rfl) ⟨1111022, by rfl⟩ : syracuseStep 1481363 = 2222045) B2222045
theorem B1481393 : Blo 984595 1481393 := bstep (se 2 (by rfl) ⟨555522, by rfl⟩ : syracuseStep 1481393 = 1111045) B1111045
theorem B1481411 : Blo 984595 1481411 := bstep (se 1 (by rfl) ⟨1111058, by rfl⟩ : syracuseStep 1481411 = 2222117) B2222117
theorem B1481441 : Blo 984595 1481441 := bstep (se 2 (by rfl) ⟨555540, by rfl⟩ : syracuseStep 1481441 = 1111081) B1111081
theorem B2104049 : Blo 984595 2104049 := bstep (se 2 (by rfl) ⟨789018, by rfl⟩ : syracuseStep 2104049 = 1578037) B1578037
theorem B1481459 : Blo 984595 1481459 := bstep (se 1 (by rfl) ⟨1111094, by rfl⟩ : syracuseStep 1481459 = 2222189) B2222189
theorem B1481489 : Blo 984595 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B1481507 : Blo 984595 1481507 := bstep (se 1 (by rfl) ⟨1111130, by rfl⟩ : syracuseStep 1481507 = 2222261) B2222261
theorem B1481537 : Blo 984595 1481537 := bstep (se 2 (by rfl) ⟨555576, by rfl⟩ : syracuseStep 1481537 = 1111153) B1111153
theorem B1481555 : Blo 984595 1481555 := bstep (se 1 (by rfl) ⟨1111166, by rfl⟩ : syracuseStep 1481555 = 2222333) B2222333
theorem B1481585 : Blo 984595 1481585 := bstep (se 2 (by rfl) ⟨555594, by rfl⟩ : syracuseStep 1481585 = 1111189) B1111189
theorem B1481603 : Blo 984595 1481603 := bstep (se 1 (by rfl) ⟨1111202, by rfl⟩ : syracuseStep 1481603 = 2222405) B2222405
theorem B1481633 : Blo 984595 1481633 := bstep (se 2 (by rfl) ⟨555612, by rfl⟩ : syracuseStep 1481633 = 1111225) B1111225
theorem B1481651 : Blo 984595 1481651 := bstep (se 1 (by rfl) ⟨1111238, by rfl⟩ : syracuseStep 1481651 = 2222477) B2222477
theorem B1874897 : Blo 984595 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B1481681 : Blo 984595 1481681 := bstep (se 2 (by rfl) ⟨555630, by rfl⟩ : syracuseStep 1481681 = 1111261) B1111261
theorem B1481699 : Blo 984595 1481699 := bstep (se 1 (by rfl) ⟨1111274, by rfl⟩ : syracuseStep 1481699 = 2222549) B2222549
theorem B13147121 : Blo 984595 13147121 := bstep (se 2 (by rfl) ⟨4930170, by rfl⟩ : syracuseStep 13147121 = 9860341) B9860341
theorem B1481729 : Blo 984595 1481729 := bstep (se 2 (by rfl) ⟨555648, by rfl⟩ : syracuseStep 1481729 = 1111297) B1111297
theorem B1481747 : Blo 984595 1481747 := bstep (se 1 (by rfl) ⟨1111310, by rfl⟩ : syracuseStep 1481747 = 2222621) B2222621
theorem B5610545 : Blo 984595 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B1481777 : Blo 984595 1481777 := bstep (se 2 (by rfl) ⟨555666, by rfl⟩ : syracuseStep 1481777 = 1111333) B1111333
theorem B1481795 : Blo 984595 1481795 := bstep (se 1 (by rfl) ⟨1111346, by rfl⟩ : syracuseStep 1481795 = 2222693) B2222693
theorem B1481825 : Blo 984595 1481825 := bstep (se 2 (by rfl) ⟨555684, by rfl⟩ : syracuseStep 1481825 = 1111369) B1111369
theorem B1481843 : Blo 984595 1481843 := bstep (se 1 (by rfl) ⟨1111382, by rfl⟩ : syracuseStep 1481843 = 2222765) B2222765
theorem B1481873 : Blo 984595 1481873 := bstep (se 2 (by rfl) ⟨555702, by rfl⟩ : syracuseStep 1481873 = 1111405) B1111405
theorem B1481891 : Blo 984595 1481891 := bstep (se 1 (by rfl) ⟨1111418, by rfl⟩ : syracuseStep 1481891 = 2222837) B2222837
theorem B1481921 : Blo 984595 1481921 := bstep (se 2 (by rfl) ⟨555720, by rfl⟩ : syracuseStep 1481921 = 1111441) B1111441
theorem B1481939 : Blo 984595 1481939 := bstep (se 1 (by rfl) ⟨1111454, by rfl⟩ : syracuseStep 1481939 = 2222909) B2222909
theorem B1481969 : Blo 984595 1481969 := bstep (se 2 (by rfl) ⟨555738, by rfl⟩ : syracuseStep 1481969 = 1111477) B1111477
theorem B1481987 : Blo 984595 1481987 := bstep (se 1 (by rfl) ⟨1111490, by rfl⟩ : syracuseStep 1481987 = 2222981) B2222981
theorem B1580305 : Blo 984595 1580305 := bstep (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) B1185229
theorem B40508693 : Blo 984595 40508693 := bstep (se 6 (by rfl) ⟨949422, by rfl⟩ : syracuseStep 40508693 = 1898845) B1898845
theorem B1482017 : Blo 984595 1482017 := bstep (se 2 (by rfl) ⟨555756, by rfl⟩ : syracuseStep 1482017 = 1111513) B1111513
theorem B1482035 : Blo 984595 1482035 := bstep (se 1 (by rfl) ⟨1111526, by rfl⟩ : syracuseStep 1482035 = 2223053) B2223053
theorem B1482065 : Blo 984595 1482065 := bstep (se 2 (by rfl) ⟨555774, by rfl⟩ : syracuseStep 1482065 = 1111549) B1111549
theorem B1482083 : Blo 984595 1482083 := bstep (se 1 (by rfl) ⟨1111562, by rfl⟩ : syracuseStep 1482083 = 2223125) B2223125
theorem B1482113 : Blo 984595 1482113 := bstep (se 2 (by rfl) ⟨555792, by rfl⟩ : syracuseStep 1482113 = 1111585) B1111585
theorem B1482131 : Blo 984595 1482131 := bstep (se 1 (by rfl) ⟨1111598, by rfl⟩ : syracuseStep 1482131 = 2223197) B2223197
theorem B1482161 : Blo 984595 1482161 := bstep (se 2 (by rfl) ⟨555810, by rfl⟩ : syracuseStep 1482161 = 1111621) B1111621
theorem B1482179 : Blo 984595 1482179 := bstep (se 1 (by rfl) ⟨1111634, by rfl⟩ : syracuseStep 1482179 = 2223269) B2223269
theorem B1482209 : Blo 984595 1482209 := bstep (se 2 (by rfl) ⟨555828, by rfl⟩ : syracuseStep 1482209 = 1111657) B1111657
theorem B4496867 : Blo 984595 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B2530801 : Blo 984595 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B1482227 : Blo 984595 1482227 := bstep (se 1 (by rfl) ⟨1111670, by rfl⟩ : syracuseStep 1482227 = 2223341) B2223341
theorem B1580561 : Blo 984595 1580561 := bstep (se 2 (by rfl) ⟨592710, by rfl⟩ : syracuseStep 1580561 = 1185421) B1185421
theorem B1482257 : Blo 984595 1482257 := bstep (se 2 (by rfl) ⟨555846, by rfl⟩ : syracuseStep 1482257 = 1111693) B1111693
theorem B1482275 : Blo 984595 1482275 := bstep (se 1 (by rfl) ⟨1111706, by rfl⟩ : syracuseStep 1482275 = 2223413) B2223413
theorem B4988465 : Blo 984595 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B1482305 : Blo 984595 1482305 := bstep (se 2 (by rfl) ⟨555864, by rfl⟩ : syracuseStep 1482305 = 1111729) B1111729
theorem B7118405 : Blo 984595 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1482323 : Blo 984595 1482323 := bstep (se 1 (by rfl) ⟨1111742, by rfl⟩ : syracuseStep 1482323 = 2223485) B2223485
theorem B2498161 : Blo 984595 2498161 := bstep (se 2 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 2498161 = 1873621) B1873621
theorem B1482353 : Blo 984595 1482353 := bstep (se 2 (by rfl) ⟨555882, by rfl⟩ : syracuseStep 1482353 = 1111765) B1111765
theorem B1482371 : Blo 984595 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B2137745 : Blo 984595 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1482401 : Blo 984595 1482401 := bstep (se 2 (by rfl) ⟨555900, by rfl⟩ : syracuseStep 1482401 = 1111801) B1111801
theorem B1482419 : Blo 984595 1482419 := bstep (se 1 (by rfl) ⟨1111814, by rfl⟩ : syracuseStep 1482419 = 2223629) B2223629
theorem B1580753 : Blo 984595 1580753 := bstep (se 2 (by rfl) ⟨592782, by rfl⟩ : syracuseStep 1580753 = 1185565) B1185565
theorem B1482449 : Blo 984595 1482449 := bstep (se 2 (by rfl) ⟨555918, by rfl⟩ : syracuseStep 1482449 = 1111837) B1111837
theorem B1482467 : Blo 984595 1482467 := bstep (se 1 (by rfl) ⟨1111850, by rfl⟩ : syracuseStep 1482467 = 2223701) B2223701
theorem B1482497 : Blo 984595 1482497 := bstep (se 2 (by rfl) ⟨555936, by rfl⟩ : syracuseStep 1482497 = 1111873) B1111873
theorem B7479053 : Blo 984595 7479053 := bstep (se 3 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 7479053 = 2804645) B2804645
theorem B10133261 : Blo 984595 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B1482515 : Blo 984595 1482515 := bstep (se 1 (by rfl) ⟨1111886, by rfl⟩ : syracuseStep 1482515 = 2223773) B2223773
theorem B1482545 : Blo 984595 1482545 := bstep (se 2 (by rfl) ⟨555954, by rfl⟩ : syracuseStep 1482545 = 1111909) B1111909
theorem B1482563 : Blo 984595 1482563 := bstep (se 1 (by rfl) ⟨1111922, by rfl⟩ : syracuseStep 1482563 = 2223845) B2223845
theorem B1875793 : Blo 984595 1875793 := bstep (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) B1406845
theorem B1482593 : Blo 984595 1482593 := bstep (se 2 (by rfl) ⟨555972, by rfl⟩ : syracuseStep 1482593 = 1111945) B1111945
theorem B1482611 : Blo 984595 1482611 := bstep (se 1 (by rfl) ⟨1111958, by rfl⟩ : syracuseStep 1482611 = 2223917) B2223917
theorem B2498435 : Blo 984595 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B1482641 : Blo 984595 1482641 := bstep (se 2 (by rfl) ⟨555990, by rfl⟩ : syracuseStep 1482641 = 1111981) B1111981
theorem B1482659 : Blo 984595 1482659 := bstep (se 1 (by rfl) ⟨1111994, by rfl⟩ : syracuseStep 1482659 = 2223989) B2223989
theorem B1482689 : Blo 984595 1482689 := bstep (se 2 (by rfl) ⟨556008, by rfl⟩ : syracuseStep 1482689 = 1112017) B1112017
theorem B1482707 : Blo 984595 1482707 := bstep (se 1 (by rfl) ⟨1112030, by rfl⟩ : syracuseStep 1482707 = 2224061) B2224061
theorem B1875953 : Blo 984595 1875953 := bstep (se 2 (by rfl) ⟨703482, by rfl⟩ : syracuseStep 1875953 = 1406965) B1406965
theorem B1482737 : Blo 984595 1482737 := bstep (se 2 (by rfl) ⟨556026, by rfl⟩ : syracuseStep 1482737 = 1112053) B1112053
theorem B2105347 : Blo 984595 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B1482755 : Blo 984595 1482755 := bstep (se 1 (by rfl) ⟨1112066, by rfl⟩ : syracuseStep 1482755 = 2224133) B2224133
theorem B1482785 : Blo 984595 1482785 := bstep (se 2 (by rfl) ⟨556044, by rfl⟩ : syracuseStep 1482785 = 1112089) B1112089
theorem B3743779 : Blo 984595 3743779 := bstep (se 1 (by rfl) ⟨2807834, by rfl⟩ : syracuseStep 3743779 = 5615669) B5615669
theorem B1482803 : Blo 984595 1482803 := bstep (se 1 (by rfl) ⟨1112102, by rfl⟩ : syracuseStep 1482803 = 2224205) B2224205
theorem B2498627 : Blo 984595 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B1482833 : Blo 984595 1482833 := bstep (se 2 (by rfl) ⟨556062, by rfl⟩ : syracuseStep 1482833 = 1112125) B1112125
theorem B1482851 : Blo 984595 1482851 := bstep (se 1 (by rfl) ⟨1112138, by rfl⟩ : syracuseStep 1482851 = 2224277) B2224277
theorem B1482881 : Blo 984595 1482881 := bstep (se 2 (by rfl) ⟨556080, by rfl⟩ : syracuseStep 1482881 = 1112161) B1112161
theorem B3285233 : Blo 984595 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B2105603 : Blo 984595 2105603 := bstep (se 1 (by rfl) ⟨1579202, by rfl⟩ : syracuseStep 2105603 = 3158405) B3158405
theorem B1777987 : Blo 984595 1777987 := bstep (se 1 (by rfl) ⟨1333490, by rfl⟩ : syracuseStep 1777987 = 2666981) B2666981
theorem B2662733 : Blo 984595 2662733 := bstep (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) B998525
theorem B16032113 : Blo 984595 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B1876355 : Blo 984595 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B5612003 : Blo 984595 5612003 := bstep (se 1 (by rfl) ⟨4209002, by rfl⟩ : syracuseStep 5612003 = 8418005) B8418005
theorem B2466289 : Blo 984595 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B8430065 : Blo 984595 8430065 := bstep (se 2 (by rfl) ⟨3161274, by rfl⟩ : syracuseStep 8430065 = 6322549) B6322549
theorem B6333005 : Blo 984595 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B1778275 : Blo 984595 1778275 := bstep (se 1 (by rfl) ⟨1333706, by rfl⟩ : syracuseStep 1778275 = 2667413) B2667413
theorem B1778449 : Blo 984595 1778449 := bstep (se 2 (by rfl) ⟨666918, by rfl⟩ : syracuseStep 1778449 = 1333837) B1333837
theorem B4989923 : Blo 984595 4989923 := bstep (se 1 (by rfl) ⟨3742442, by rfl⟩ : syracuseStep 4989923 = 7484885) B7484885
theorem B2499569 : Blo 984595 2499569 := bstep (se 2 (by rfl) ⟨937338, by rfl⟩ : syracuseStep 2499569 = 1874677) B1874677
theorem B1582067 : Blo 984595 1582067 := bstep (se 1 (by rfl) ⟨1186550, by rfl⟩ : syracuseStep 1582067 = 2373101) B2373101
theorem B2499619 : Blo 984595 2499619 := bstep (se 1 (by rfl) ⟨1874714, by rfl⟩ : syracuseStep 2499619 = 3749429) B3749429
theorem B2499761 : Blo 984595 2499761 := bstep (se 2 (by rfl) ⟨937410, by rfl⟩ : syracuseStep 2499761 = 1874821) B1874821
theorem B2106577 : Blo 984595 2106577 := bstep (se 2 (by rfl) ⟨789966, by rfl⟩ : syracuseStep 2106577 = 1579933) B1579933
theorem B1582291 : Blo 984595 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B1582355 : Blo 984595 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B1582483 : Blo 984595 1582483 := bstep (se 1 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 1582483 = 2373725) B2373725
theorem B2663857 : Blo 984595 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B1779313 : Blo 984595 1779313 := bstep (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) B1334485
theorem B4990733 : Blo 984595 4990733 := bstep (se 3 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 4990733 = 1871525) B1871525
theorem B2107235 : Blo 984595 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B3549041 : Blo 984595 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B6006641 : Blo 984595 6006641 := bstep (se 2 (by rfl) ⟨2252490, by rfl⟩ : syracuseStep 6006641 = 4504981) B4504981
theorem B7579619 : Blo 984595 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B2566129 : Blo 984595 2566129 := bstep (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) B1924597
theorem B1124339 : Blo 984595 1124339 := bstep (se 1 (by rfl) ⟨843254, by rfl⟩ : syracuseStep 1124339 = 1686509) B1686509
theorem B1583201 : Blo 984595 1583201 := bstep (se 2 (by rfl) ⟨593700, by rfl⟩ : syracuseStep 1583201 = 1187401) B1187401
theorem B2500753 : Blo 984595 2500753 := bstep (se 2 (by rfl) ⟨937782, by rfl⟩ : syracuseStep 2500753 = 1875565) B1875565
theorem B3745997 : Blo 984595 3745997 := bstep (se 3 (by rfl) ⟨702374, by rfl⟩ : syracuseStep 3745997 = 1404749) B1404749
theorem B1583329 : Blo 984595 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B5613893 : Blo 984595 5613893 := bstep (se 4 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 5613893 = 1052605) B1052605
theorem B2501027 : Blo 984595 2501027 := bstep (se 1 (by rfl) ⟨1875770, by rfl⟩ : syracuseStep 2501027 = 3751541) B3751541
theorem B8006129 : Blo 984595 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B2501219 : Blo 984595 2501219 := bstep (se 1 (by rfl) ⟨1875914, by rfl⟩ : syracuseStep 2501219 = 3751829) B3751829
theorem B7481969 : Blo 984595 7481969 := bstep (se 2 (by rfl) ⟨2805738, by rfl⟩ : syracuseStep 7481969 = 5611477) B5611477
theorem B2534033 : Blo 984595 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B2108081 : Blo 984595 2108081 := bstep (se 2 (by rfl) ⟨790530, by rfl⟩ : syracuseStep 2108081 = 1581061) B1581061
theorem B2534179 : Blo 984595 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B8432525 : Blo 984595 8432525 := bstep (se 3 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 8432525 = 3162197) B3162197
theorem B3156995 : Blo 984595 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B2502161 : Blo 984595 2502161 := bstep (se 2 (by rfl) ⟨938310, by rfl⟩ : syracuseStep 2502161 = 1876621) B1876621
theorem B2666029 : Blo 984595 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B2502211 : Blo 984595 2502211 := bstep (se 1 (by rfl) ⟨1876658, by rfl⟩ : syracuseStep 2502211 = 3753317) B3753317
theorem B2502353 : Blo 984595 2502353 := bstep (se 2 (by rfl) ⟨938382, by rfl⟩ : syracuseStep 2502353 = 1876765) B1876765
theorem B3157841 : Blo 984595 3157841 := bstep (se 2 (by rfl) ⟨1184190, by rfl⟩ : syracuseStep 3157841 = 2368381) B2368381
theorem B8335685 : Blo 984595 8335685 := bstep (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) B1562941
theorem B2666893 : Blo 984595 2666893 := bstep (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) B1000085
theorem B4993649 : Blo 984595 4993649 := bstep (se 2 (by rfl) ⟨1872618, by rfl⟩ : syracuseStep 4993649 = 3745237) B3745237
theorem B2569073 : Blo 984595 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B3748913 : Blo 984595 3748913 := bstep (se 2 (by rfl) ⟨1405842, by rfl⟩ : syracuseStep 3748913 = 2811685) B2811685
theorem B1684579 : Blo 984595 1684579 := bstep (se 1 (by rfl) ⟨1263434, by rfl⟩ : syracuseStep 1684579 = 2526869) B2526869
theorem B12629105 : Blo 984595 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B15971525 : Blo 984595 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B1684739 : Blo 984595 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B3323213 : Blo 984595 3323213 := bstep (se 3 (by rfl) ⟨623102, by rfl⟩ : syracuseStep 3323213 = 1246205) B1246205
theorem B3323267 : Blo 984595 3323267 := bstep (se 1 (by rfl) ⟨2492450, by rfl⟩ : syracuseStep 3323267 = 4984901) B4984901
theorem B2110865 : Blo 984595 2110865 := bstep (se 2 (by rfl) ⟨791574, by rfl⟩ : syracuseStep 2110865 = 1583149) B1583149
theorem B3159661 : Blo 984595 3159661 := bstep (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) B1184873
theorem B3323537 : Blo 984595 3323537 := bstep (se 2 (by rfl) ⟨1246326, by rfl⟩ : syracuseStep 3323537 = 2492653) B2492653
theorem B2668355 : Blo 984595 2668355 := bstep (se 1 (by rfl) ⟨2001266, by rfl⟩ : syracuseStep 2668355 = 4002533) B4002533
theorem B4995107 : Blo 984595 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B11384945 : Blo 984595 11384945 := bstep (se 2 (by rfl) ⟨4269354, by rfl⟩ : syracuseStep 11384945 = 8538709) B8538709
theorem B3324077 : Blo 984595 3324077 := bstep (se 3 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 3324077 = 1246529) B1246529
theorem B1685729 : Blo 984595 1685729 := bstep (se 2 (by rfl) ⟨632148, by rfl⟩ : syracuseStep 1685729 = 1264297) B1264297
theorem B3324131 : Blo 984595 3324131 := bstep (se 1 (by rfl) ⟨2493098, by rfl⟩ : syracuseStep 3324131 = 4986197) B4986197
theorem B4208867 : Blo 984595 4208867 := bstep (se 1 (by rfl) ⟨3156650, by rfl⟩ : syracuseStep 4208867 = 6313301) B6313301
theorem B3750371 : Blo 984595 3750371 := bstep (se 1 (by rfl) ⟨2812778, by rfl⟩ : syracuseStep 3750371 = 5625557) B5625557
theorem B3324401 : Blo 984595 3324401 := bstep (se 2 (by rfl) ⟨1246650, by rfl⟩ : syracuseStep 3324401 = 2493301) B2493301
theorem B4995917 : Blo 984595 4995917 := bstep (se 3 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 4995917 = 1873469) B1873469
theorem B2669489 : Blo 984595 2669489 := bstep (se 2 (by rfl) ⟨1001058, by rfl⟩ : syracuseStep 2669489 = 2002117) B2002117
theorem B3324941 : Blo 984595 3324941 := bstep (se 3 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 3324941 = 1246853) B1246853
theorem B3324995 : Blo 984595 3324995 := bstep (se 1 (by rfl) ⟨2493746, by rfl⟩ : syracuseStep 3324995 = 4987493) B4987493
theorem B3554417 : Blo 984595 3554417 := bstep (se 2 (by rfl) ⟨1332906, by rfl⟩ : syracuseStep 3554417 = 2665813) B2665813
theorem B2997425 : Blo 984595 2997425 := bstep (se 2 (by rfl) ⟨1124034, by rfl⟩ : syracuseStep 2997425 = 2248069) B2248069
theorem B4504909 : Blo 984595 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B3325265 : Blo 984595 3325265 := bstep (se 2 (by rfl) ⟨1246974, by rfl⟩ : syracuseStep 3325265 = 2493949) B2493949
theorem B5684579 : Blo 984595 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B3554765 : Blo 984595 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B3751373 : Blo 984595 3751373 := bstep (se 3 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 3751373 = 1406765) B1406765
theorem B12631565 : Blo 984595 12631565 := bstep (se 3 (by rfl) ⟨2368418, by rfl⟩ : syracuseStep 12631565 = 4736837) B4736837
theorem B2375185 : Blo 984595 2375185 := bstep (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) B1781389
theorem B1687331 : Blo 984595 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B3325805 : Blo 984595 3325805 := bstep (se 3 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 3325805 = 1247177) B1247177
theorem B3325859 : Blo 984595 3325859 := bstep (se 1 (by rfl) ⟨2494394, by rfl⟩ : syracuseStep 3325859 = 4988789) B4988789
theorem B5619725 : Blo 984595 5619725 := bstep (se 3 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 5619725 = 2107397) B2107397
theorem B3326129 : Blo 984595 3326129 := bstep (se 2 (by rfl) ⟨1247298, by rfl⟩ : syracuseStep 3326129 = 2494597) B2494597
theorem B4210865 : Blo 984595 4210865 := bstep (se 2 (by rfl) ⟨1579074, by rfl⟩ : syracuseStep 4210865 = 3158149) B3158149
theorem B999875 : Blo 984595 999875 := bstep (se 1 (by rfl) ⟨749906, by rfl⟩ : syracuseStep 999875 = 1499813) B1499813
theorem B1688131 : Blo 984595 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B3326669 : Blo 984595 3326669 := bstep (se 3 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 3326669 = 1247501) B1247501
theorem B4506353 : Blo 984595 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B3326723 : Blo 984595 3326723 := bstep (se 1 (by rfl) ⟨2495042, by rfl⟩ : syracuseStep 3326723 = 4990085) B4990085
theorem B2671501 : Blo 984595 2671501 := bstep (se 3 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 2671501 = 1001813) B1001813
theorem B5686193 : Blo 984595 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B3163121 : Blo 984595 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B3326993 : Blo 984595 3326993 := bstep (se 2 (by rfl) ⟨1247622, by rfl⟩ : syracuseStep 3326993 = 2495245) B2495245
theorem B3163313 : Blo 984595 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B4113713 : Blo 984595 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B3753485 : Blo 984595 3753485 := bstep (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) B1407557
theorem B3327533 : Blo 984595 3327533 := bstep (se 3 (by rfl) ⟨623912, by rfl⟩ : syracuseStep 3327533 = 1247825) B1247825
theorem B3327587 : Blo 984595 3327587 := bstep (se 1 (by rfl) ⟨2495690, by rfl⟩ : syracuseStep 3327587 = 4991381) B4991381
theorem B4998833 : Blo 984595 4998833 := bstep (se 2 (by rfl) ⟨1874562, by rfl⟩ : syracuseStep 4998833 = 3749125) B3749125
theorem B1689395 : Blo 984595 1689395 := bstep (se 1 (by rfl) ⟨1267046, by rfl⟩ : syracuseStep 1689395 = 2534093) B2534093
theorem B4212557 : Blo 984595 4212557 := bstep (se 3 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 4212557 = 1579709) B1579709
theorem B3327857 : Blo 984595 3327857 := bstep (se 2 (by rfl) ⟨1247946, by rfl⟩ : syracuseStep 3327857 = 2495893) B2495893
theorem B11225141 : Blo 984595 11225141 := bstep (se 5 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 11225141 = 1052357) B1052357
theorem B2803825 : Blo 984595 2803825 := bstep (se 2 (by rfl) ⟨1051434, by rfl⟩ : syracuseStep 2803825 = 2102869) B2102869
theorem B5621957 : Blo 984595 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B3328397 : Blo 984595 3328397 := bstep (se 3 (by rfl) ⟨624074, by rfl⟩ : syracuseStep 3328397 = 1248149) B1248149
theorem B3328451 : Blo 984595 3328451 := bstep (se 1 (by rfl) ⟨2496338, by rfl⟩ : syracuseStep 3328451 = 4992677) B4992677
theorem B3557965 : Blo 984595 3557965 := bstep (se 3 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 3557965 = 1334237) B1334237
theorem B3328721 : Blo 984595 3328721 := bstep (se 2 (by rfl) ⟨1248270, by rfl⟩ : syracuseStep 3328721 = 2496541) B2496541
theorem B1690355 : Blo 984595 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B5622641 : Blo 984595 5622641 := bstep (se 2 (by rfl) ⟨2108490, by rfl⟩ : syracuseStep 5622641 = 4216981) B4216981
theorem B5000291 : Blo 984595 5000291 := bstep (se 1 (by rfl) ⟨3750218, by rfl⟩ : syracuseStep 5000291 = 7500437) B7500437
theorem B9489635 : Blo 984595 9489635 := bstep (se 1 (by rfl) ⟨7117226, by rfl⟩ : syracuseStep 9489635 = 14234453) B14234453
theorem B3329261 : Blo 984595 3329261 := bstep (se 3 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 3329261 = 1248473) B1248473
theorem B3329315 : Blo 984595 3329315 := bstep (se 1 (by rfl) ⟨2496986, by rfl⟩ : syracuseStep 3329315 = 4993973) B4993973
theorem B2805101 : Blo 984595 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B3165581 : Blo 984595 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B2805283 : Blo 984595 2805283 := bstep (se 1 (by rfl) ⟨2103962, by rfl⟩ : syracuseStep 2805283 = 4207925) B4207925
theorem B3329585 : Blo 984595 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B2805329 : Blo 984595 2805329 := bstep (se 2 (by rfl) ⟨1051998, by rfl⟩ : syracuseStep 2805329 = 2103997) B2103997
theorem B2215601 : Blo 984595 2215601 := bstep (se 2 (by rfl) ⟨830850, by rfl⟩ : syracuseStep 2215601 = 1661701) B1661701
theorem B2215619 : Blo 984595 2215619 := bstep (se 1 (by rfl) ⟨1661714, by rfl⟩ : syracuseStep 2215619 = 3323429) B3323429
theorem B1330993 : Blo 984595 1330993 := bstep (se 2 (by rfl) ⟨499122, by rfl⟩ : syracuseStep 1330993 = 998245) B998245
theorem B5001101 : Blo 984595 5001101 := bstep (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) B1875413
theorem B2215889 : Blo 984595 2215889 := bstep (se 2 (by rfl) ⟨830958, by rfl⟩ : syracuseStep 2215889 = 1661917) B1661917
theorem B2215907 : Blo 984595 2215907 := bstep (se 1 (by rfl) ⟨1661930, by rfl⟩ : syracuseStep 2215907 = 3323861) B3323861
theorem B12144653 : Blo 984595 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B3330125 : Blo 984595 3330125 := bstep (se 3 (by rfl) ⟨624398, by rfl⟩ : syracuseStep 3330125 = 1248797) B1248797
theorem B3330179 : Blo 984595 3330179 := bstep (se 1 (by rfl) ⟨2497634, by rfl⟩ : syracuseStep 3330179 = 4995269) B4995269
theorem B2216177 : Blo 984595 2216177 := bstep (se 2 (by rfl) ⟨831066, by rfl⟩ : syracuseStep 2216177 = 1662133) B1662133
theorem B2216195 : Blo 984595 2216195 := bstep (se 1 (by rfl) ⟨1662146, by rfl⟩ : syracuseStep 2216195 = 3324293) B3324293
theorem B5624099 : Blo 984595 5624099 := bstep (se 1 (by rfl) ⟨4218074, by rfl⟩ : syracuseStep 5624099 = 8436149) B8436149
theorem B3330449 : Blo 984595 3330449 := bstep (se 2 (by rfl) ⟨1248918, by rfl⟩ : syracuseStep 3330449 = 2497837) B2497837
theorem B2216465 : Blo 984595 2216465 := bstep (se 2 (by rfl) ⟨831174, by rfl⟩ : syracuseStep 2216465 = 1662349) B1662349
theorem B2216483 : Blo 984595 2216483 := bstep (se 1 (by rfl) ⟨1662362, by rfl⟩ : syracuseStep 2216483 = 3324725) B3324725
theorem B2216753 : Blo 984595 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B2216771 : Blo 984595 2216771 := bstep (se 1 (by rfl) ⟨1662578, by rfl⟩ : syracuseStep 2216771 = 3325157) B3325157
theorem B3330989 : Blo 984595 3330989 := bstep (se 3 (by rfl) ⟨624560, by rfl⟩ : syracuseStep 3330989 = 1249121) B1249121
theorem B3331043 : Blo 984595 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B2806787 : Blo 984595 2806787 := bstep (se 1 (by rfl) ⟨2105090, by rfl⟩ : syracuseStep 2806787 = 4210181) B4210181
theorem B2217041 : Blo 984595 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B2217059 : Blo 984595 2217059 := bstep (se 1 (by rfl) ⟨1662794, by rfl⟩ : syracuseStep 2217059 = 3325589) B3325589
theorem B3331313 : Blo 984595 3331313 := bstep (se 2 (by rfl) ⟨1249242, by rfl⟩ : syracuseStep 3331313 = 2498485) B2498485
theorem B2217329 : Blo 984595 2217329 := bstep (se 2 (by rfl) ⟨831498, by rfl⟩ : syracuseStep 2217329 = 1662997) B1662997
theorem B2217347 : Blo 984595 2217347 := bstep (se 1 (by rfl) ⟨1663010, by rfl⟩ : syracuseStep 2217347 = 3326021) B3326021
theorem B3003857 : Blo 984595 3003857 := bstep (se 2 (by rfl) ⟨1126446, by rfl⟩ : syracuseStep 3003857 = 2252893) B2252893
theorem B5199331 : Blo 984595 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B6739469 : Blo 984595 6739469 := bstep (se 3 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 6739469 = 2527301) B2527301
theorem B3200561 : Blo 984595 3200561 := bstep (se 2 (by rfl) ⟨1200210, by rfl⟩ : syracuseStep 3200561 = 2400421) B2400421
theorem B2217617 : Blo 984595 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B2217635 : Blo 984595 2217635 := bstep (se 1 (by rfl) ⟨1663226, by rfl⟩ : syracuseStep 2217635 = 3326453) B3326453
theorem B6313733 : Blo 984595 6313733 := bstep (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) B1183825
theorem B3331853 : Blo 984595 3331853 := bstep (se 3 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 3331853 = 1249445) B1249445
theorem B15980341 : Blo 984595 15980341 := bstep (se 5 (by rfl) ⟨749078, by rfl⟩ : syracuseStep 15980341 = 1498157) B1498157
theorem B3331907 : Blo 984595 3331907 := bstep (se 1 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 3331907 = 4997861) B4997861
theorem B1333139 : Blo 984595 1333139 := bstep (se 1 (by rfl) ⟨999854, by rfl⟩ : syracuseStep 1333139 = 1999709) B1999709
theorem B2217905 : Blo 984595 2217905 := bstep (se 2 (by rfl) ⟨831714, by rfl⟩ : syracuseStep 2217905 = 1663429) B1663429
theorem B2217923 : Blo 984595 2217923 := bstep (se 1 (by rfl) ⟨1663442, by rfl⟩ : syracuseStep 2217923 = 3326885) B3326885
theorem B3004465 : Blo 984595 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B3332177 : Blo 984595 3332177 := bstep (se 2 (by rfl) ⟨1249566, by rfl⟩ : syracuseStep 3332177 = 2499133) B2499133
theorem B4216931 : Blo 984595 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2218193 : Blo 984595 2218193 := bstep (se 2 (by rfl) ⟨831822, by rfl⟩ : syracuseStep 2218193 = 1663645) B1663645
theorem B2808017 : Blo 984595 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B66771157 : Blo 984595 66771157 := bstep (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) B1564949
theorem B2218211 : Blo 984595 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B2218481 : Blo 984595 2218481 := bstep (se 2 (by rfl) ⟨831930, by rfl⟩ : syracuseStep 2218481 = 1663861) B1663861
theorem B2218499 : Blo 984595 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B1661539 : Blo 984595 1661539 := bstep (se 1 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 1661539 = 2492309) B2492309
theorem B3332717 : Blo 984595 3332717 := bstep (se 3 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 3332717 = 1249769) B1249769
theorem B13523597 : Blo 984595 13523597 := bstep (se 3 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 13523597 = 5071349) B5071349
theorem B3332771 : Blo 984595 3332771 := bstep (se 1 (by rfl) ⟨2499578, by rfl⟩ : syracuseStep 3332771 = 4999157) B4999157
theorem B1661681 : Blo 984595 1661681 := bstep (se 2 (by rfl) ⟨623130, by rfl⟩ : syracuseStep 1661681 = 1246261) B1246261
theorem B5004017 : Blo 984595 5004017 := bstep (se 2 (by rfl) ⟨1876506, by rfl⟩ : syracuseStep 5004017 = 3753013) B3753013
theorem B2218769 : Blo 984595 2218769 := bstep (se 2 (by rfl) ⟨832038, by rfl⟩ : syracuseStep 2218769 = 1664077) B1664077
theorem B2218787 : Blo 984595 2218787 := bstep (se 1 (by rfl) ⟨1664090, by rfl⟩ : syracuseStep 2218787 = 3328181) B3328181
theorem B1661809 : Blo 984595 1661809 := bstep (se 2 (by rfl) ⟨623178, by rfl⟩ : syracuseStep 1661809 = 1246357) B1246357
theorem B18963341 : Blo 984595 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B1661843 : Blo 984595 1661843 := bstep (se 1 (by rfl) ⟨1246382, by rfl⟩ : syracuseStep 1661843 = 2492765) B2492765
theorem B3333041 : Blo 984595 3333041 := bstep (se 2 (by rfl) ⟨1249890, by rfl⟩ : syracuseStep 3333041 = 2499781) B2499781
theorem B1661971 : Blo 984595 1661971 := bstep (se 1 (by rfl) ⟨1246478, by rfl⟩ : syracuseStep 1661971 = 2492957) B2492957
theorem B2219057 : Blo 984595 2219057 := bstep (se 2 (by rfl) ⟨832146, by rfl⟩ : syracuseStep 2219057 = 1664293) B1664293
theorem B5069873 : Blo 984595 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B2219075 : Blo 984595 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B1662113 : Blo 984595 1662113 := bstep (se 2 (by rfl) ⟨623292, by rfl⟩ : syracuseStep 1662113 = 1246585) B1246585
theorem B1662241 : Blo 984595 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B1662275 : Blo 984595 1662275 := bstep (se 1 (by rfl) ⟨1246706, by rfl⟩ : syracuseStep 1662275 = 2493413) B2493413
theorem B2219345 : Blo 984595 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B2219363 : Blo 984595 2219363 := bstep (se 1 (by rfl) ⟨1664522, by rfl⟩ : syracuseStep 2219363 = 3329045) B3329045
theorem B1498547 : Blo 984595 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B1662403 : Blo 984595 1662403 := bstep (se 1 (by rfl) ⟨1246802, by rfl⟩ : syracuseStep 1662403 = 2493605) B2493605
theorem B5627333 : Blo 984595 5627333 := bstep (se 4 (by rfl) ⟨527562, by rfl⟩ : syracuseStep 5627333 = 1055125) B1055125
theorem B3333581 : Blo 984595 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B3333635 : Blo 984595 3333635 := bstep (se 1 (by rfl) ⟨2500226, by rfl⟩ : syracuseStep 3333635 = 5000453) B5000453
theorem B1662545 : Blo 984595 1662545 := bstep (se 2 (by rfl) ⟨623454, by rfl⟩ : syracuseStep 1662545 = 1246909) B1246909
theorem B2219633 : Blo 984595 2219633 := bstep (se 2 (by rfl) ⟨832362, by rfl⟩ : syracuseStep 2219633 = 1664725) B1664725
theorem B2219651 : Blo 984595 2219651 := bstep (se 1 (by rfl) ⟨1664738, by rfl⟩ : syracuseStep 2219651 = 3329477) B3329477
theorem B2809475 : Blo 984595 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B4742819 : Blo 984595 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B1662673 : Blo 984595 1662673 := bstep (se 2 (by rfl) ⟨623502, by rfl⟩ : syracuseStep 1662673 = 1247005) B1247005
theorem B1662707 : Blo 984595 1662707 := bstep (se 1 (by rfl) ⟨1247030, by rfl⟩ : syracuseStep 1662707 = 2494061) B2494061
theorem B3333905 : Blo 984595 3333905 := bstep (se 2 (by rfl) ⟨1250214, by rfl⟩ : syracuseStep 3333905 = 2500429) B2500429
theorem B1498961 : Blo 984595 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1662835 : Blo 984595 1662835 := bstep (se 1 (by rfl) ⟨1247126, by rfl⟩ : syracuseStep 1662835 = 2494253) B2494253
theorem B1335155 : Blo 984595 1335155 := bstep (se 1 (by rfl) ⟨1001366, by rfl⟩ : syracuseStep 1335155 = 2002733) B2002733
theorem B5627789 : Blo 984595 5627789 := bstep (se 3 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 5627789 = 2110421) B2110421
theorem B25681805 : Blo 984595 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B2219921 : Blo 984595 2219921 := bstep (se 2 (by rfl) ⟨832470, by rfl⟩ : syracuseStep 2219921 = 1664941) B1664941
theorem B2219939 : Blo 984595 2219939 := bstep (se 1 (by rfl) ⟨1664954, by rfl⟩ : syracuseStep 2219939 = 3329909) B3329909
theorem B2252785 : Blo 984595 2252785 := bstep (se 2 (by rfl) ⟨844794, by rfl⟩ : syracuseStep 2252785 = 1689589) B1689589
theorem B1662977 : Blo 984595 1662977 := bstep (se 2 (by rfl) ⟨623616, by rfl⟩ : syracuseStep 1662977 = 1247233) B1247233
theorem B4218929 : Blo 984595 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B8413253 : Blo 984595 8413253 := bstep (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) B1577485
theorem B1663105 : Blo 984595 1663105 := bstep (se 2 (by rfl) ⟨623664, by rfl⟩ : syracuseStep 1663105 = 1247329) B1247329
theorem B5693581 : Blo 984595 5693581 := bstep (se 3 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 5693581 = 2135093) B2135093
theorem B1663139 : Blo 984595 1663139 := bstep (se 1 (by rfl) ⟨1247354, by rfl⟩ : syracuseStep 1663139 = 2494709) B2494709
theorem B2220209 : Blo 984595 2220209 := bstep (se 2 (by rfl) ⟨832578, by rfl⟩ : syracuseStep 2220209 = 1665157) B1665157
theorem B2220227 : Blo 984595 2220227 := bstep (se 1 (by rfl) ⟨1665170, by rfl⟩ : syracuseStep 2220227 = 3330341) B3330341
theorem B1499393 : Blo 984595 1499393 := bstep (se 2 (by rfl) ⟨562272, by rfl⟩ : syracuseStep 1499393 = 1124545) B1124545
theorem B2253059 : Blo 984595 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B1663267 : Blo 984595 1663267 := bstep (se 1 (by rfl) ⟨1247450, by rfl⟩ : syracuseStep 1663267 = 2494901) B2494901
theorem B3334445 : Blo 984595 3334445 := bstep (se 3 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 3334445 = 1250417) B1250417
theorem B3334499 : Blo 984595 3334499 := bstep (se 1 (by rfl) ⟨2500874, by rfl⟩ : syracuseStep 3334499 = 5001749) B5001749
theorem B6316451 : Blo 984595 6316451 := bstep (se 1 (by rfl) ⟨4737338, by rfl⟩ : syracuseStep 6316451 = 9474677) B9474677
theorem B2810285 : Blo 984595 2810285 := bstep (se 3 (by rfl) ⟨526928, by rfl⟩ : syracuseStep 2810285 = 1053857) B1053857
theorem B1663409 : Blo 984595 1663409 := bstep (se 2 (by rfl) ⟨623778, by rfl⟩ : syracuseStep 1663409 = 1247557) B1247557
theorem B2220497 : Blo 984595 2220497 := bstep (se 2 (by rfl) ⟨832686, by rfl⟩ : syracuseStep 2220497 = 1665373) B1665373
theorem B2220515 : Blo 984595 2220515 := bstep (se 1 (by rfl) ⟨1665386, by rfl⟩ : syracuseStep 2220515 = 3330773) B3330773
theorem B1663537 : Blo 984595 1663537 := bstep (se 2 (by rfl) ⟨623826, by rfl⟩ : syracuseStep 1663537 = 1247653) B1247653
theorem B1663571 : Blo 984595 1663571 := bstep (se 1 (by rfl) ⟨1247678, by rfl⟩ : syracuseStep 1663571 = 2495357) B2495357
theorem B1335907 : Blo 984595 1335907 := bstep (se 1 (by rfl) ⟨1001930, by rfl⟩ : syracuseStep 1335907 = 2003861) B2003861
theorem B2810477 : Blo 984595 2810477 := bstep (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) B1053929
theorem B3334769 : Blo 984595 3334769 := bstep (se 2 (by rfl) ⟨1250538, by rfl⟩ : syracuseStep 3334769 = 2501077) B2501077
theorem B5333701 : Blo 984595 5333701 := bstep (se 4 (by rfl) ⟨500034, by rfl⟩ : syracuseStep 5333701 = 1000069) B1000069
theorem B1663699 : Blo 984595 1663699 := bstep (se 1 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 1663699 = 2495549) B2495549
theorem B2220785 : Blo 984595 2220785 := bstep (se 2 (by rfl) ⟨832794, by rfl⟩ : syracuseStep 2220785 = 1665589) B1665589
theorem B10674929 : Blo 984595 10674929 := bstep (se 2 (by rfl) ⟨4003098, by rfl⟩ : syracuseStep 10674929 = 8006197) B8006197
theorem B2220803 : Blo 984595 2220803 := bstep (se 1 (by rfl) ⟨1665602, by rfl⟩ : syracuseStep 2220803 = 3331205) B3331205
theorem B1663841 : Blo 984595 1663841 := bstep (se 2 (by rfl) ⟨623940, by rfl⟩ : syracuseStep 1663841 = 1247881) B1247881
theorem B16835525 : Blo 984595 16835525 := bstep (se 4 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 16835525 = 3156661) B3156661
theorem B1663969 : Blo 984595 1663969 := bstep (se 2 (by rfl) ⟨623988, by rfl⟩ : syracuseStep 1663969 = 1247977) B1247977
theorem B25617379 : Blo 984595 25617379 := bstep (se 1 (by rfl) ⟨19213034, by rfl⟩ : syracuseStep 25617379 = 38426069) B38426069
theorem B1664003 : Blo 984595 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B2221073 : Blo 984595 2221073 := bstep (se 2 (by rfl) ⟨832902, by rfl⟩ : syracuseStep 2221073 = 1665805) B1665805
theorem B2221091 : Blo 984595 2221091 := bstep (se 1 (by rfl) ⟨1665818, by rfl⟩ : syracuseStep 2221091 = 3331637) B3331637
theorem B3793997 : Blo 984595 3793997 := bstep (se 3 (by rfl) ⟨711374, by rfl⟩ : syracuseStep 3793997 = 1422749) B1422749
theorem B1664131 : Blo 984595 1664131 := bstep (se 1 (by rfl) ⟨1248098, by rfl⟩ : syracuseStep 1664131 = 2496197) B2496197
theorem B3335309 : Blo 984595 3335309 := bstep (se 3 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 3335309 = 1250741) B1250741
theorem B3335363 : Blo 984595 3335363 := bstep (se 1 (by rfl) ⟨2501522, by rfl⟩ : syracuseStep 3335363 = 5003045) B5003045
theorem B1500385 : Blo 984595 1500385 := bstep (se 2 (by rfl) ⟨562644, by rfl⟩ : syracuseStep 1500385 = 1125289) B1125289
theorem B1664273 : Blo 984595 1664273 := bstep (se 2 (by rfl) ⟨624102, by rfl⟩ : syracuseStep 1664273 = 1248205) B1248205
theorem B2221361 : Blo 984595 2221361 := bstep (se 2 (by rfl) ⟨833010, by rfl⟩ : syracuseStep 2221361 = 1666021) B1666021
theorem B2221379 : Blo 984595 2221379 := bstep (se 1 (by rfl) ⟨1666034, by rfl⟩ : syracuseStep 2221379 = 3332069) B3332069
theorem B1664401 : Blo 984595 1664401 := bstep (se 2 (by rfl) ⟨624150, by rfl⟩ : syracuseStep 1664401 = 1248301) B1248301
theorem B2254225 : Blo 984595 2254225 := bstep (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) B1690669
theorem B1664435 : Blo 984595 1664435 := bstep (se 1 (by rfl) ⟨1248326, by rfl⟩ : syracuseStep 1664435 = 2496653) B2496653
theorem B3335633 : Blo 984595 3335633 := bstep (se 2 (by rfl) ⟨1250862, by rfl⟩ : syracuseStep 3335633 = 2501725) B2501725
theorem B10118641 : Blo 984595 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B1500689 : Blo 984595 1500689 := bstep (se 2 (by rfl) ⟨562758, by rfl⟩ : syracuseStep 1500689 = 1125517) B1125517
theorem B1664563 : Blo 984595 1664563 := bstep (se 1 (by rfl) ⟨1248422, by rfl⟩ : syracuseStep 1664563 = 2496845) B2496845
theorem B2811469 : Blo 984595 2811469 := bstep (se 3 (by rfl) ⟨527150, by rfl⟩ : syracuseStep 2811469 = 1054301) B1054301
theorem B2221649 : Blo 984595 2221649 := bstep (se 2 (by rfl) ⟨833118, by rfl⟩ : syracuseStep 2221649 = 1666237) B1666237
theorem B2221667 : Blo 984595 2221667 := bstep (se 1 (by rfl) ⟨1666250, by rfl⟩ : syracuseStep 2221667 = 3332501) B3332501
theorem B25585265 : Blo 984595 25585265 := bstep (se 2 (by rfl) ⟨9594474, by rfl⟩ : syracuseStep 25585265 = 19188949) B19188949
theorem B1664705 : Blo 984595 1664705 := bstep (se 2 (by rfl) ⟨624264, by rfl⟩ : syracuseStep 1664705 = 1248529) B1248529
theorem B1599203 : Blo 984595 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B1107715 : Blo 984595 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B1664833 : Blo 984595 1664833 := bstep (se 2 (by rfl) ⟨624312, by rfl⟩ : syracuseStep 1664833 = 1248625) B1248625
theorem B1664867 : Blo 984595 1664867 := bstep (se 1 (by rfl) ⟨1248650, by rfl⟩ : syracuseStep 1664867 = 2497301) B2497301
theorem B2221937 : Blo 984595 2221937 := bstep (se 2 (by rfl) ⟨833226, by rfl⟩ : syracuseStep 2221937 = 1666453) B1666453
theorem B9496433 : Blo 984595 9496433 := bstep (se 2 (by rfl) ⟨3561162, by rfl⟩ : syracuseStep 9496433 = 7122325) B7122325
theorem B2221955 : Blo 984595 2221955 := bstep (se 1 (by rfl) ⟨1666466, by rfl⟩ : syracuseStep 2221955 = 3332933) B3332933
theorem B1107859 : Blo 984595 1107859 := bstep (se 1 (by rfl) ⟨830894, by rfl⟩ : syracuseStep 1107859 = 1661789) B1661789
theorem B2779085 : Blo 984595 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B1664995 : Blo 984595 1664995 := bstep (se 1 (by rfl) ⟨1248746, by rfl⟩ : syracuseStep 1664995 = 2497493) B2497493
theorem B3336173 : Blo 984595 3336173 := bstep (se 3 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 3336173 = 1251065) B1251065
theorem B1108003 : Blo 984595 1108003 := bstep (se 1 (by rfl) ⟨831002, by rfl⟩ : syracuseStep 1108003 = 1662005) B1662005
theorem B1402915 : Blo 984595 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B3336227 : Blo 984595 3336227 := bstep (se 1 (by rfl) ⟨2502170, by rfl⟩ : syracuseStep 3336227 = 5004341) B5004341
theorem B1665137 : Blo 984595 1665137 := bstep (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) B1248853
theorem B1599619 : Blo 984595 1599619 := bstep (se 1 (by rfl) ⟨1199714, by rfl⟩ : syracuseStep 1599619 = 2399429) B2399429
theorem B2222225 : Blo 984595 2222225 := bstep (se 2 (by rfl) ⟨833334, by rfl⟩ : syracuseStep 2222225 = 1666669) B1666669
theorem B2222243 : Blo 984595 2222243 := bstep (se 1 (by rfl) ⟨1666682, by rfl⟩ : syracuseStep 2222243 = 3333365) B3333365
theorem B1108147 : Blo 984595 1108147 := bstep (se 1 (by rfl) ⟨831110, by rfl⟩ : syracuseStep 1108147 = 1662221) B1662221
theorem B2844877 : Blo 984595 2844877 := bstep (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) B1066829
theorem B1665265 : Blo 984595 1665265 := bstep (se 2 (by rfl) ⟨624474, by rfl⟩ : syracuseStep 1665265 = 1248949) B1248949
theorem B1665299 : Blo 984595 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B3336497 : Blo 984595 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B1108291 : Blo 984595 1108291 := bstep (se 1 (by rfl) ⟨831218, by rfl⟩ : syracuseStep 1108291 = 1662437) B1662437
theorem B6318449 : Blo 984595 6318449 := bstep (se 2 (by rfl) ⟨2369418, by rfl⟩ : syracuseStep 6318449 = 4738837) B4738837
theorem B1665427 : Blo 984595 1665427 := bstep (se 1 (by rfl) ⟨1249070, by rfl⟩ : syracuseStep 1665427 = 2498141) B2498141
theorem B2222513 : Blo 984595 2222513 := bstep (se 2 (by rfl) ⟨833442, by rfl⟩ : syracuseStep 2222513 = 1666885) B1666885
theorem B2222531 : Blo 984595 2222531 := bstep (se 1 (by rfl) ⟨1666898, by rfl⟩ : syracuseStep 2222531 = 3333797) B3333797
theorem B4221389 : Blo 984595 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B1108435 : Blo 984595 1108435 := bstep (se 1 (by rfl) ⟨831326, by rfl⟩ : syracuseStep 1108435 = 1662653) B1662653
theorem B1665569 : Blo 984595 1665569 := bstep (se 2 (by rfl) ⟨624588, by rfl⟩ : syracuseStep 1665569 = 1249177) B1249177
theorem B3041837 : Blo 984595 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B1108579 : Blo 984595 1108579 := bstep (se 1 (by rfl) ⟨831434, by rfl⟩ : syracuseStep 1108579 = 1662869) B1662869
theorem B1665697 : Blo 984595 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B1665731 : Blo 984595 1665731 := bstep (se 1 (by rfl) ⟨1249298, by rfl⟩ : syracuseStep 1665731 = 2498597) B2498597
theorem B2222801 : Blo 984595 2222801 := bstep (se 2 (by rfl) ⟨833550, by rfl⟩ : syracuseStep 2222801 = 1667101) B1667101
theorem B2222819 : Blo 984595 2222819 := bstep (se 1 (by rfl) ⟨1667114, by rfl⟩ : syracuseStep 2222819 = 3334229) B3334229
theorem B1108723 : Blo 984595 1108723 := bstep (se 1 (by rfl) ⟨831542, by rfl⟩ : syracuseStep 1108723 = 1663085) B1663085
theorem B12151565 : Blo 984595 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B9497357 : Blo 984595 9497357 := bstep (se 3 (by rfl) ⟨1780754, by rfl⟩ : syracuseStep 9497357 = 3561509) B3561509
theorem B1665859 : Blo 984595 1665859 := bstep (se 1 (by rfl) ⟨1249394, by rfl⟩ : syracuseStep 1665859 = 2498789) B2498789
theorem B1108867 : Blo 984595 1108867 := bstep (se 1 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 1108867 = 1663301) B1663301
theorem B1666001 : Blo 984595 1666001 := bstep (se 2 (by rfl) ⟨624750, by rfl⟩ : syracuseStep 1666001 = 1249501) B1249501
theorem B2223089 : Blo 984595 2223089 := bstep (se 2 (by rfl) ⟨833658, by rfl⟩ : syracuseStep 2223089 = 1667317) B1667317
theorem B2223107 : Blo 984595 2223107 := bstep (se 1 (by rfl) ⟨1667330, by rfl⟩ : syracuseStep 2223107 = 3334661) B3334661
theorem B1109011 : Blo 984595 1109011 := bstep (se 1 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 1109011 = 1663517) B1663517
theorem B1666129 : Blo 984595 1666129 := bstep (se 2 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 1666129 = 1249597) B1249597
theorem B1666163 : Blo 984595 1666163 := bstep (se 1 (by rfl) ⟨1249622, by rfl⟩ : syracuseStep 1666163 = 2499245) B2499245
theorem B1404049 : Blo 984595 1404049 := bstep (se 2 (by rfl) ⟨526518, by rfl⟩ : syracuseStep 1404049 = 1053037) B1053037
theorem B1109155 : Blo 984595 1109155 := bstep (se 1 (by rfl) ⟨831866, by rfl⟩ : syracuseStep 1109155 = 1663733) B1663733
theorem B7498979 : Blo 984595 7498979 := bstep (se 1 (by rfl) ⟨5624234, by rfl⟩ : syracuseStep 7498979 = 11248469) B11248469
theorem B1404145 : Blo 984595 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B1666291 : Blo 984595 1666291 := bstep (se 1 (by rfl) ⟨1249718, by rfl⟩ : syracuseStep 1666291 = 2499437) B2499437
theorem B4746509 : Blo 984595 4746509 := bstep (se 3 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 4746509 = 1779941) B1779941
theorem B2813201 : Blo 984595 2813201 := bstep (se 2 (by rfl) ⟨1054950, by rfl⟩ : syracuseStep 2813201 = 2109901) B2109901
theorem B2223377 : Blo 984595 2223377 := bstep (se 2 (by rfl) ⟨833766, by rfl⟩ : syracuseStep 2223377 = 1667533) B1667533
theorem B2223395 : Blo 984595 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B1109299 : Blo 984595 1109299 := bstep (se 1 (by rfl) ⟨831974, by rfl⟩ : syracuseStep 1109299 = 1663949) B1663949
theorem B1666433 : Blo 984595 1666433 := bstep (se 2 (by rfl) ⟨624912, by rfl⟩ : syracuseStep 1666433 = 1249825) B1249825
theorem B1109443 : Blo 984595 1109443 := bstep (se 1 (by rfl) ⟨832082, by rfl⟩ : syracuseStep 1109443 = 1664165) B1664165
theorem B2813393 : Blo 984595 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B1502707 : Blo 984595 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B1666561 : Blo 984595 1666561 := bstep (se 2 (by rfl) ⟨624960, by rfl⟩ : syracuseStep 1666561 = 1249921) B1249921
theorem B1666595 : Blo 984595 1666595 := bstep (se 1 (by rfl) ⟨1249946, by rfl⟩ : syracuseStep 1666595 = 2499893) B2499893
theorem B2223665 : Blo 984595 2223665 := bstep (se 2 (by rfl) ⟨833874, by rfl⟩ : syracuseStep 2223665 = 1667749) B1667749
theorem B2223683 : Blo 984595 2223683 := bstep (se 1 (by rfl) ⟨1667762, by rfl⟩ : syracuseStep 2223683 = 3335525) B3335525
theorem B1109587 : Blo 984595 1109587 := bstep (se 1 (by rfl) ⟨832190, by rfl⟩ : syracuseStep 1109587 = 1664381) B1664381
theorem B3370609 : Blo 984595 3370609 := bstep (se 2 (by rfl) ⟨1263978, by rfl⟩ : syracuseStep 3370609 = 2527957) B2527957
theorem B1666723 : Blo 984595 1666723 := bstep (se 1 (by rfl) ⟨1250042, by rfl⟩ : syracuseStep 1666723 = 2500085) B2500085
theorem B5992141 : Blo 984595 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B1404641 : Blo 984595 1404641 := bstep (se 2 (by rfl) ⟨526740, by rfl⟩ : syracuseStep 1404641 = 1053481) B1053481
theorem B1109731 : Blo 984595 1109731 := bstep (se 1 (by rfl) ⟨832298, by rfl⟩ : syracuseStep 1109731 = 1664597) B1664597
theorem B1502963 : Blo 984595 1502963 := bstep (se 1 (by rfl) ⟨1127222, by rfl⟩ : syracuseStep 1502963 = 2254445) B2254445
theorem B1601281 : Blo 984595 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B1666865 : Blo 984595 1666865 := bstep (se 2 (by rfl) ⟨625074, by rfl⟩ : syracuseStep 1666865 = 1250149) B1250149
theorem B26963765 : Blo 984595 26963765 := bstep (se 5 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 26963765 = 2527853) B2527853
theorem B2223953 : Blo 984595 2223953 := bstep (se 2 (by rfl) ⟨833982, by rfl⟩ : syracuseStep 2223953 = 1667965) B1667965
theorem B2223971 : Blo 984595 2223971 := bstep (se 1 (by rfl) ⟨1667978, by rfl⟩ : syracuseStep 2223971 = 3335957) B3335957
theorem B1109875 : Blo 984595 1109875 := bstep (se 1 (by rfl) ⟨832406, by rfl⟩ : syracuseStep 1109875 = 1664813) B1664813
theorem B1666993 : Blo 984595 1666993 := bstep (se 2 (by rfl) ⟨625122, by rfl⟩ : syracuseStep 1666993 = 1250245) B1250245
theorem B1667027 : Blo 984595 1667027 := bstep (se 1 (by rfl) ⟨1250270, by rfl⟩ : syracuseStep 1667027 = 2500541) B2500541
theorem B1110019 : Blo 984595 1110019 := bstep (se 1 (by rfl) ⟨832514, by rfl⟩ : syracuseStep 1110019 = 1665029) B1665029
theorem B1667155 : Blo 984595 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B2224241 : Blo 984595 2224241 := bstep (se 2 (by rfl) ⟨834090, by rfl⟩ : syracuseStep 2224241 = 1668181) B1668181
theorem B2224259 : Blo 984595 2224259 := bstep (se 1 (by rfl) ⟨1668194, by rfl⟩ : syracuseStep 2224259 = 3336389) B3336389
theorem B1110163 : Blo 984595 1110163 := bstep (se 1 (by rfl) ⟨832622, by rfl⟩ : syracuseStep 1110163 = 1665245) B1665245
theorem B1667297 : Blo 984595 1667297 := bstep (se 2 (by rfl) ⟨625236, by rfl⟩ : syracuseStep 1667297 = 1250473) B1250473
theorem B1110307 : Blo 984595 1110307 := bstep (se 1 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 1110307 = 1665461) B1665461
theorem B1667425 : Blo 984595 1667425 := bstep (se 2 (by rfl) ⟨625284, by rfl⟩ : syracuseStep 1667425 = 1250569) B1250569
theorem B1667459 : Blo 984595 1667459 := bstep (se 1 (by rfl) ⟨1250594, by rfl⟩ : syracuseStep 1667459 = 2501189) B2501189
theorem B2814385 : Blo 984595 2814385 := bstep (se 2 (by rfl) ⟨1055394, by rfl⟩ : syracuseStep 2814385 = 2110789) B2110789
theorem B1110451 : Blo 984595 1110451 := bstep (se 1 (by rfl) ⟨832838, by rfl⟩ : syracuseStep 1110451 = 1665677) B1665677
theorem B1667587 : Blo 984595 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B1405507 : Blo 984595 1405507 := bstep (se 1 (by rfl) ⟨1054130, by rfl⟩ : syracuseStep 1405507 = 2108261) B2108261
theorem B1110595 : Blo 984595 1110595 := bstep (se 1 (by rfl) ⟨832946, by rfl⟩ : syracuseStep 1110595 = 1665893) B1665893
theorem B1667729 : Blo 984595 1667729 := bstep (se 2 (by rfl) ⟨625398, by rfl⟩ : syracuseStep 1667729 = 1250797) B1250797
theorem B1405603 : Blo 984595 1405603 := bstep (se 1 (by rfl) ⟨1054202, by rfl⟩ : syracuseStep 1405603 = 2108405) B2108405
theorem B2814659 : Blo 984595 2814659 := bstep (se 1 (by rfl) ⟨2110994, by rfl⟩ : syracuseStep 2814659 = 4221989) B4221989
theorem B1110739 : Blo 984595 1110739 := bstep (se 1 (by rfl) ⟨833054, by rfl⟩ : syracuseStep 1110739 = 1666109) B1666109
theorem B6320909 : Blo 984595 6320909 := bstep (se 3 (by rfl) ⟨1185170, by rfl⟩ : syracuseStep 6320909 = 2370341) B2370341
theorem B1667857 : Blo 984595 1667857 := bstep (se 2 (by rfl) ⟨625446, by rfl⟩ : syracuseStep 1667857 = 1250893) B1250893
theorem B1667891 : Blo 984595 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B1110883 : Blo 984595 1110883 := bstep (se 1 (by rfl) ⟨833162, by rfl⟩ : syracuseStep 1110883 = 1666325) B1666325
theorem B3208045 : Blo 984595 3208045 := bstep (se 3 (by rfl) ⟨601508, by rfl⟩ : syracuseStep 3208045 = 1203017) B1203017
theorem B2814851 : Blo 984595 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B1668019 : Blo 984595 1668019 := bstep (se 1 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 1668019 = 2502029) B2502029
theorem B1111027 : Blo 984595 1111027 := bstep (se 1 (by rfl) ⟨833270, by rfl⟩ : syracuseStep 1111027 = 1666541) B1666541
theorem B1668161 : Blo 984595 1668161 := bstep (se 2 (by rfl) ⟨625560, by rfl⟩ : syracuseStep 1668161 = 1251121) B1251121
theorem B7599203 : Blo 984595 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B4813937 : Blo 984595 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B1111171 : Blo 984595 1111171 := bstep (se 1 (by rfl) ⟨833378, by rfl⟩ : syracuseStep 1111171 = 1666757) B1666757
theorem B1406099 : Blo 984595 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B1111315 : Blo 984595 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B1111459 : Blo 984595 1111459 := bstep (se 1 (by rfl) ⟨833594, by rfl⟩ : syracuseStep 1111459 = 1667189) B1667189
theorem B11236805 : Blo 984595 11236805 := bstep (se 4 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 11236805 = 2106901) B2106901
theorem B1111603 : Blo 984595 1111603 := bstep (se 1 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 1111603 = 1667405) B1667405
theorem B1111747 : Blo 984595 1111747 := bstep (se 1 (by rfl) ⟨833810, by rfl⟩ : syracuseStep 1111747 = 1667621) B1667621
theorem B1406737 : Blo 984595 1406737 := bstep (se 2 (by rfl) ⟨527526, by rfl⟩ : syracuseStep 1406737 = 1055053) B1055053
theorem B1111891 : Blo 984595 1111891 := bstep (se 1 (by rfl) ⟨833918, by rfl⟩ : syracuseStep 1111891 = 1667837) B1667837
theorem B1112035 : Blo 984595 1112035 := bstep (se 1 (by rfl) ⟨834026, by rfl⟩ : syracuseStep 1112035 = 1668053) B1668053
theorem B1407073 : Blo 984595 1407073 := bstep (se 2 (by rfl) ⟨527652, by rfl⟩ : syracuseStep 1407073 = 1055305) B1055305
theorem B1013891 : Blo 984595 1013891 := bstep (se 1 (by rfl) ⟨760418, by rfl⟩ : syracuseStep 1013891 = 1520837) B1520837
theorem B4553059 : Blo 984595 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B1800835 : Blo 984595 1800835 := bstep (se 1 (by rfl) ⟨1350626, by rfl⟩ : syracuseStep 1800835 = 2701253) B2701253
theorem B5995235 : Blo 984595 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B1604483 : Blo 984595 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B2882531 : Blo 984595 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B3374083 : Blo 984595 3374083 := bstep (se 1 (by rfl) ⟨2530562, by rfl⟩ : syracuseStep 3374083 = 5061125) B5061125
theorem B4062221 : Blo 984595 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B8421317 : Blo 984595 8421317 := bstep (se 4 (by rfl) ⟨789498, by rfl⟩ : syracuseStep 8421317 = 1578997) B1578997
theorem B1442443 : Blo 984595 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B7111601 : Blo 984595 7111601 := bstep (se 2 (by rfl) ⟨2666850, by rfl⟩ : syracuseStep 7111601 = 5333701) B5333701
theorem B3998899 : Blo 984595 3998899 := bstep (se 1 (by rfl) ⟨2999174, by rfl⟩ : syracuseStep 3998899 = 5998349) B5998349
theorem B1246423 : Blo 984595 1246423 := bstep (se 1 (by rfl) ⟨934817, by rfl⟩ : syracuseStep 1246423 = 1869635) B1869635
theorem B984599 : Blo 984595 984599 := bstep (se 1 (by rfl) ⟨738449, by rfl⟩ : syracuseStep 984599 = 1476899) B1476899
theorem B984619 : Blo 984595 984619 := bstep (se 1 (by rfl) ⟨738464, by rfl⟩ : syracuseStep 984619 = 1476929) B1476929
theorem B984631 : Blo 984595 984631 := bstep (se 1 (by rfl) ⟨738473, by rfl⟩ : syracuseStep 984631 = 1476947) B1476947
theorem B984651 : Blo 984595 984651 := bstep (se 1 (by rfl) ⟨738488, by rfl⟩ : syracuseStep 984651 = 1476977) B1476977
theorem B984663 : Blo 984595 984663 := bstep (se 1 (by rfl) ⟨738497, by rfl⟩ : syracuseStep 984663 = 1476995) B1476995
theorem B984683 : Blo 984595 984683 := bstep (se 1 (by rfl) ⟨738512, by rfl⟩ : syracuseStep 984683 = 1477025) B1477025
theorem B984695 : Blo 984595 984695 := bstep (se 1 (by rfl) ⟨738521, by rfl⟩ : syracuseStep 984695 = 1477043) B1477043
theorem B2000513 : Blo 984595 2000513 := bstep (se 2 (by rfl) ⟨750192, by rfl⟩ : syracuseStep 2000513 = 1500385) B1500385
theorem B984715 : Blo 984595 984715 := bstep (se 1 (by rfl) ⟨738536, by rfl⟩ : syracuseStep 984715 = 1477073) B1477073
theorem B984727 : Blo 984595 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B984747 : Blo 984595 984747 := bstep (se 1 (by rfl) ⟨738560, by rfl⟩ : syracuseStep 984747 = 1477121) B1477121
theorem B984759 : Blo 984595 984759 := bstep (se 1 (by rfl) ⟨738569, by rfl⟩ : syracuseStep 984759 = 1477139) B1477139
theorem B984779 : Blo 984595 984779 := bstep (se 1 (by rfl) ⟨738584, by rfl⟩ : syracuseStep 984779 = 1477169) B1477169
theorem B984791 : Blo 984595 984791 := bstep (se 1 (by rfl) ⟨738593, by rfl⟩ : syracuseStep 984791 = 1477187) B1477187
theorem B984811 : Blo 984595 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B984823 : Blo 984595 984823 := bstep (se 1 (by rfl) ⟨738617, by rfl⟩ : syracuseStep 984823 = 1477235) B1477235
theorem B984843 : Blo 984595 984843 := bstep (se 1 (by rfl) ⟨738632, by rfl⟩ : syracuseStep 984843 = 1477265) B1477265
theorem B984855 : Blo 984595 984855 := bstep (se 1 (by rfl) ⟨738641, by rfl⟩ : syracuseStep 984855 = 1477283) B1477283
theorem B984875 : Blo 984595 984875 := bstep (se 1 (by rfl) ⟨738656, by rfl⟩ : syracuseStep 984875 = 1477313) B1477313
theorem B984887 : Blo 984595 984887 := bstep (se 1 (by rfl) ⟨738665, by rfl⟩ : syracuseStep 984887 = 1477331) B1477331
theorem B984907 : Blo 984595 984907 := bstep (se 1 (by rfl) ⟨738680, by rfl⟩ : syracuseStep 984907 = 1477361) B1477361
theorem B3999563 : Blo 984595 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B984919 : Blo 984595 984919 := bstep (se 1 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 984919 = 1477379) B1477379
theorem B984939 : Blo 984595 984939 := bstep (se 1 (by rfl) ⟨738704, by rfl⟩ : syracuseStep 984939 = 1477409) B1477409
theorem B984951 : Blo 984595 984951 := bstep (se 1 (by rfl) ⟨738713, by rfl⟩ : syracuseStep 984951 = 1477427) B1477427
theorem B984971 : Blo 984595 984971 := bstep (se 1 (by rfl) ⟨738728, by rfl⟩ : syracuseStep 984971 = 1477457) B1477457
theorem B984983 : Blo 984595 984983 := bstep (se 1 (by rfl) ⟨738737, by rfl⟩ : syracuseStep 984983 = 1477475) B1477475
theorem B985003 : Blo 984595 985003 := bstep (se 1 (by rfl) ⟨738752, by rfl⟩ : syracuseStep 985003 = 1477505) B1477505
theorem B985015 : Blo 984595 985015 := bstep (se 1 (by rfl) ⟨738761, by rfl⟩ : syracuseStep 985015 = 1477523) B1477523
theorem B985035 : Blo 984595 985035 := bstep (se 1 (by rfl) ⟨738776, by rfl⟩ : syracuseStep 985035 = 1477553) B1477553
theorem B985047 : Blo 984595 985047 := bstep (se 1 (by rfl) ⟨738785, by rfl⟩ : syracuseStep 985047 = 1477571) B1477571
theorem B985067 : Blo 984595 985067 := bstep (se 1 (by rfl) ⟨738800, by rfl⟩ : syracuseStep 985067 = 1477601) B1477601
theorem B985079 : Blo 984595 985079 := bstep (se 1 (by rfl) ⟨738809, by rfl⟩ : syracuseStep 985079 = 1477619) B1477619
theorem B985099 : Blo 984595 985099 := bstep (se 1 (by rfl) ⟨738824, by rfl⟩ : syracuseStep 985099 = 1477649) B1477649
theorem B985111 : Blo 984595 985111 := bstep (se 1 (by rfl) ⟨738833, by rfl⟩ : syracuseStep 985111 = 1477667) B1477667
theorem B985131 : Blo 984595 985131 := bstep (se 1 (by rfl) ⟨738848, by rfl⟩ : syracuseStep 985131 = 1477697) B1477697
theorem B985143 : Blo 984595 985143 := bstep (se 1 (by rfl) ⟨738857, by rfl⟩ : syracuseStep 985143 = 1477715) B1477715
theorem B2492491 : Blo 984595 2492491 := bstep (se 1 (by rfl) ⟨1869368, by rfl⟩ : syracuseStep 2492491 = 3738737) B3738737
theorem B985163 : Blo 984595 985163 := bstep (se 1 (by rfl) ⟨738872, by rfl⟩ : syracuseStep 985163 = 1477745) B1477745
theorem B985175 : Blo 984595 985175 := bstep (se 1 (by rfl) ⟨738881, by rfl⟩ : syracuseStep 985175 = 1477763) B1477763
theorem B985195 : Blo 984595 985195 := bstep (se 1 (by rfl) ⟨738896, by rfl⟩ : syracuseStep 985195 = 1477793) B1477793
theorem B985207 : Blo 984595 985207 := bstep (se 1 (by rfl) ⟨738905, by rfl⟩ : syracuseStep 985207 = 1477811) B1477811
theorem B985227 : Blo 984595 985227 := bstep (se 1 (by rfl) ⟨738920, by rfl⟩ : syracuseStep 985227 = 1477841) B1477841
theorem B985239 : Blo 984595 985239 := bstep (se 1 (by rfl) ⟨738929, by rfl⟩ : syracuseStep 985239 = 1477859) B1477859
theorem B6326423 : Blo 984595 6326423 := bstep (se 1 (by rfl) ⟨4744817, by rfl⟩ : syracuseStep 6326423 = 9489635) B9489635
theorem B985259 : Blo 984595 985259 := bstep (se 1 (by rfl) ⟨738944, by rfl⟩ : syracuseStep 985259 = 1477889) B1477889
theorem B985271 : Blo 984595 985271 := bstep (se 1 (by rfl) ⟨738953, by rfl⟩ : syracuseStep 985271 = 1477907) B1477907
theorem B985291 : Blo 984595 985291 := bstep (se 1 (by rfl) ⟨738968, by rfl⟩ : syracuseStep 985291 = 1477937) B1477937
theorem B985303 : Blo 984595 985303 := bstep (se 1 (by rfl) ⟨738977, by rfl⟩ : syracuseStep 985303 = 1477955) B1477955
theorem B2492633 : Blo 984595 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B985323 : Blo 984595 985323 := bstep (se 1 (by rfl) ⟨738992, by rfl⟩ : syracuseStep 985323 = 1477985) B1477985
theorem B1870067 : Blo 984595 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B985335 : Blo 984595 985335 := bstep (se 1 (by rfl) ⟨739001, by rfl⟩ : syracuseStep 985335 = 1478003) B1478003
theorem B985355 : Blo 984595 985355 := bstep (se 1 (by rfl) ⟨739016, by rfl⟩ : syracuseStep 985355 = 1478033) B1478033
theorem B985367 : Blo 984595 985367 := bstep (se 1 (by rfl) ⟨739025, by rfl⟩ : syracuseStep 985367 = 1478051) B1478051
theorem B985387 : Blo 984595 985387 := bstep (se 1 (by rfl) ⟨739040, by rfl⟩ : syracuseStep 985387 = 1478081) B1478081
theorem B6850861 : Blo 984595 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B985399 : Blo 984595 985399 := bstep (se 1 (by rfl) ⟨739049, by rfl⟩ : syracuseStep 985399 = 1478099) B1478099
theorem B985419 : Blo 984595 985419 := bstep (se 1 (by rfl) ⟨739064, by rfl⟩ : syracuseStep 985419 = 1478129) B1478129
theorem B985431 : Blo 984595 985431 := bstep (se 1 (by rfl) ⟨739073, by rfl⟩ : syracuseStep 985431 = 1478147) B1478147
theorem B1476953 : Blo 984595 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B7506269 : Blo 984595 7506269 := bstep (se 3 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 7506269 = 2814851) B2814851
theorem B985451 : Blo 984595 985451 := bstep (se 1 (by rfl) ⟨739088, by rfl⟩ : syracuseStep 985451 = 1478177) B1478177
theorem B985463 : Blo 984595 985463 := bstep (se 1 (by rfl) ⟨739097, by rfl⟩ : syracuseStep 985463 = 1478195) B1478195
theorem B1870219 : Blo 984595 1870219 := bstep (se 1 (by rfl) ⟨1402664, by rfl⟩ : syracuseStep 1870219 = 2805329) B2805329
theorem B985483 : Blo 984595 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B985495 : Blo 984595 985495 := bstep (se 1 (by rfl) ⟨739121, by rfl⟩ : syracuseStep 985495 = 1478243) B1478243
theorem B985515 : Blo 984595 985515 := bstep (se 1 (by rfl) ⟨739136, by rfl⟩ : syracuseStep 985515 = 1478273) B1478273
theorem B985527 : Blo 984595 985527 := bstep (se 1 (by rfl) ⟨739145, by rfl⟩ : syracuseStep 985527 = 1478291) B1478291
theorem B1477067 : Blo 984595 1477067 := bstep (se 1 (by rfl) ⟨1107800, by rfl⟩ : syracuseStep 1477067 = 2215601) B2215601
theorem B985547 : Blo 984595 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B1477079 : Blo 984595 1477079 := bstep (se 1 (by rfl) ⟨1107809, by rfl⟩ : syracuseStep 1477079 = 2215619) B2215619
theorem B985559 : Blo 984595 985559 := bstep (se 1 (by rfl) ⟨739169, by rfl⟩ : syracuseStep 985559 = 1478339) B1478339
theorem B985579 : Blo 984595 985579 := bstep (se 1 (by rfl) ⟨739184, by rfl⟩ : syracuseStep 985579 = 1478369) B1478369
theorem B985591 : Blo 984595 985591 := bstep (se 1 (by rfl) ⟨739193, by rfl⟩ : syracuseStep 985591 = 1478387) B1478387
theorem B985611 : Blo 984595 985611 := bstep (se 1 (by rfl) ⟨739208, by rfl⟩ : syracuseStep 985611 = 1478417) B1478417
theorem B985623 : Blo 984595 985623 := bstep (se 1 (by rfl) ⟨739217, by rfl⟩ : syracuseStep 985623 = 1478435) B1478435
theorem B1477145 : Blo 984595 1477145 := bstep (se 2 (by rfl) ⟨553929, by rfl⟩ : syracuseStep 1477145 = 1107859) B1107859
theorem B985643 : Blo 984595 985643 := bstep (se 1 (by rfl) ⟨739232, by rfl⟩ : syracuseStep 985643 = 1478465) B1478465
theorem B985655 : Blo 984595 985655 := bstep (se 1 (by rfl) ⟨739241, by rfl⟩ : syracuseStep 985655 = 1478483) B1478483
theorem B985675 : Blo 984595 985675 := bstep (se 1 (by rfl) ⟨739256, by rfl⟩ : syracuseStep 985675 = 1478513) B1478513
theorem B985687 : Blo 984595 985687 := bstep (se 1 (by rfl) ⟨739265, by rfl⟩ : syracuseStep 985687 = 1478531) B1478531
theorem B985707 : Blo 984595 985707 := bstep (se 1 (by rfl) ⟨739280, by rfl⟩ : syracuseStep 985707 = 1478561) B1478561
theorem B985719 : Blo 984595 985719 := bstep (se 1 (by rfl) ⟨739289, by rfl⟩ : syracuseStep 985719 = 1478579) B1478579
theorem B1477259 : Blo 984595 1477259 := bstep (se 1 (by rfl) ⟨1107944, by rfl⟩ : syracuseStep 1477259 = 2215889) B2215889
theorem B985739 : Blo 984595 985739 := bstep (se 1 (by rfl) ⟨739304, by rfl⟩ : syracuseStep 985739 = 1478609) B1478609
theorem B1477271 : Blo 984595 1477271 := bstep (se 1 (by rfl) ⟨1107953, by rfl⟩ : syracuseStep 1477271 = 2215907) B2215907
theorem B985751 : Blo 984595 985751 := bstep (se 1 (by rfl) ⟨739313, by rfl⟩ : syracuseStep 985751 = 1478627) B1478627
theorem B985771 : Blo 984595 985771 := bstep (se 1 (by rfl) ⟨739328, by rfl⟩ : syracuseStep 985771 = 1478657) B1478657
theorem B8096435 : Blo 984595 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B985783 : Blo 984595 985783 := bstep (se 1 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 985783 = 1478675) B1478675
theorem B985803 : Blo 984595 985803 := bstep (se 1 (by rfl) ⟨739352, by rfl⟩ : syracuseStep 985803 = 1478705) B1478705
theorem B985815 : Blo 984595 985815 := bstep (se 1 (by rfl) ⟨739361, by rfl⟩ : syracuseStep 985815 = 1478723) B1478723
theorem B1477337 : Blo 984595 1477337 := bstep (se 2 (by rfl) ⟨554001, by rfl⟩ : syracuseStep 1477337 = 1108003) B1108003
theorem B1870553 : Blo 984595 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B985835 : Blo 984595 985835 := bstep (se 1 (by rfl) ⟨739376, by rfl⟩ : syracuseStep 985835 = 1478753) B1478753
theorem B985847 : Blo 984595 985847 := bstep (se 1 (by rfl) ⟨739385, by rfl⟩ : syracuseStep 985847 = 1478771) B1478771
theorem B985867 : Blo 984595 985867 := bstep (se 1 (by rfl) ⟨739400, by rfl⟩ : syracuseStep 985867 = 1478801) B1478801
theorem B985879 : Blo 984595 985879 := bstep (se 1 (by rfl) ⟨739409, by rfl⟩ : syracuseStep 985879 = 1478819) B1478819
theorem B985899 : Blo 984595 985899 := bstep (se 1 (by rfl) ⟨739424, by rfl⟩ : syracuseStep 985899 = 1478849) B1478849
theorem B3738419 : Blo 984595 3738419 := bstep (se 1 (by rfl) ⟨2803814, by rfl⟩ : syracuseStep 3738419 = 5607629) B5607629
theorem B985911 : Blo 984595 985911 := bstep (se 1 (by rfl) ⟨739433, by rfl⟩ : syracuseStep 985911 = 1478867) B1478867
theorem B3738433 : Blo 984595 3738433 := bstep (se 2 (by rfl) ⟨1401912, by rfl⟩ : syracuseStep 3738433 = 2803825) B2803825
theorem B1477451 : Blo 984595 1477451 := bstep (se 1 (by rfl) ⟨1108088, by rfl⟩ : syracuseStep 1477451 = 2216177) B2216177
theorem B985931 : Blo 984595 985931 := bstep (se 1 (by rfl) ⟨739448, by rfl⟩ : syracuseStep 985931 = 1478897) B1478897
theorem B1477463 : Blo 984595 1477463 := bstep (se 1 (by rfl) ⟨1108097, by rfl⟩ : syracuseStep 1477463 = 2216195) B2216195
theorem B985943 : Blo 984595 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B2132825 : Blo 984595 2132825 := bstep (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) B1599619
theorem B1051499 : Blo 984595 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B985963 : Blo 984595 985963 := bstep (se 1 (by rfl) ⟨739472, by rfl⟩ : syracuseStep 985963 = 1478945) B1478945
theorem B985975 : Blo 984595 985975 := bstep (se 1 (by rfl) ⟨739481, by rfl⟩ : syracuseStep 985975 = 1478963) B1478963
theorem B985995 : Blo 984595 985995 := bstep (se 1 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 985995 = 1478993) B1478993
theorem B1248139 : Blo 984595 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B986007 : Blo 984595 986007 := bstep (se 1 (by rfl) ⟨739505, by rfl⟩ : syracuseStep 986007 = 1479011) B1479011
theorem B1477529 : Blo 984595 1477529 := bstep (se 2 (by rfl) ⟨554073, by rfl⟩ : syracuseStep 1477529 = 1108147) B1108147
theorem B986027 : Blo 984595 986027 := bstep (se 1 (by rfl) ⟨739520, by rfl⟩ : syracuseStep 986027 = 1479041) B1479041
theorem B986039 : Blo 984595 986039 := bstep (se 1 (by rfl) ⟨739529, by rfl⟩ : syracuseStep 986039 = 1479059) B1479059
theorem B986059 : Blo 984595 986059 := bstep (se 1 (by rfl) ⟨739544, by rfl⟩ : syracuseStep 986059 = 1479089) B1479089
theorem B986071 : Blo 984595 986071 := bstep (se 1 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 986071 = 1479107) B1479107
theorem B986091 : Blo 984595 986091 := bstep (se 1 (by rfl) ⟨739568, by rfl⟩ : syracuseStep 986091 = 1479137) B1479137
theorem B986103 : Blo 984595 986103 := bstep (se 1 (by rfl) ⟨739577, by rfl⟩ : syracuseStep 986103 = 1479155) B1479155
theorem B1477643 : Blo 984595 1477643 := bstep (se 1 (by rfl) ⟨1108232, by rfl⟩ : syracuseStep 1477643 = 2216465) B2216465
theorem B986123 : Blo 984595 986123 := bstep (se 1 (by rfl) ⟨739592, by rfl⟩ : syracuseStep 986123 = 1479185) B1479185
theorem B2493463 : Blo 984595 2493463 := bstep (se 1 (by rfl) ⟨1870097, by rfl⟩ : syracuseStep 2493463 = 3740195) B3740195
theorem B1477655 : Blo 984595 1477655 := bstep (se 1 (by rfl) ⟨1108241, by rfl⟩ : syracuseStep 1477655 = 2216483) B2216483
theorem B986135 : Blo 984595 986135 := bstep (se 1 (by rfl) ⟨739601, by rfl⟩ : syracuseStep 986135 = 1479203) B1479203
theorem B986155 : Blo 984595 986155 := bstep (se 1 (by rfl) ⟨739616, by rfl⟩ : syracuseStep 986155 = 1479233) B1479233
theorem B986167 : Blo 984595 986167 := bstep (se 1 (by rfl) ⟨739625, by rfl⟩ : syracuseStep 986167 = 1479251) B1479251
theorem B986187 : Blo 984595 986187 := bstep (se 1 (by rfl) ⟨739640, by rfl⟩ : syracuseStep 986187 = 1479281) B1479281
theorem B986199 : Blo 984595 986199 := bstep (se 1 (by rfl) ⟨739649, by rfl⟩ : syracuseStep 986199 = 1479299) B1479299
theorem B1477721 : Blo 984595 1477721 := bstep (se 2 (by rfl) ⟨554145, by rfl⟩ : syracuseStep 1477721 = 1108291) B1108291
theorem B986219 : Blo 984595 986219 := bstep (se 1 (by rfl) ⟨739664, by rfl⟩ : syracuseStep 986219 = 1479329) B1479329
theorem B986231 : Blo 984595 986231 := bstep (se 1 (by rfl) ⟨739673, by rfl⟩ : syracuseStep 986231 = 1479347) B1479347
theorem B986251 : Blo 984595 986251 := bstep (se 1 (by rfl) ⟨739688, by rfl⟩ : syracuseStep 986251 = 1479377) B1479377
theorem B986263 : Blo 984595 986263 := bstep (se 1 (by rfl) ⟨739697, by rfl⟩ : syracuseStep 986263 = 1479395) B1479395
theorem B986283 : Blo 984595 986283 := bstep (se 1 (by rfl) ⟨739712, by rfl⟩ : syracuseStep 986283 = 1479425) B1479425
theorem B986295 : Blo 984595 986295 := bstep (se 1 (by rfl) ⟨739721, by rfl⟩ : syracuseStep 986295 = 1479443) B1479443
theorem B1477835 : Blo 984595 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B986315 : Blo 984595 986315 := bstep (se 1 (by rfl) ⟨739736, by rfl⟩ : syracuseStep 986315 = 1479473) B1479473
theorem B1477847 : Blo 984595 1477847 := bstep (se 1 (by rfl) ⟨1108385, by rfl⟩ : syracuseStep 1477847 = 2216771) B2216771
theorem B986327 : Blo 984595 986327 := bstep (se 1 (by rfl) ⟨739745, by rfl⟩ : syracuseStep 986327 = 1479491) B1479491
theorem B986347 : Blo 984595 986347 := bstep (se 1 (by rfl) ⟨739760, by rfl⟩ : syracuseStep 986347 = 1479521) B1479521
theorem B986359 : Blo 984595 986359 := bstep (se 1 (by rfl) ⟨739769, by rfl⟩ : syracuseStep 986359 = 1479539) B1479539
theorem B986379 : Blo 984595 986379 := bstep (se 1 (by rfl) ⟨739784, by rfl⟩ : syracuseStep 986379 = 1479569) B1479569
theorem B986391 : Blo 984595 986391 := bstep (se 1 (by rfl) ⟨739793, by rfl⟩ : syracuseStep 986391 = 1479587) B1479587
theorem B1477913 : Blo 984595 1477913 := bstep (se 2 (by rfl) ⟨554217, by rfl⟩ : syracuseStep 1477913 = 1108435) B1108435
theorem B986411 : Blo 984595 986411 := bstep (se 1 (by rfl) ⟨739808, by rfl⟩ : syracuseStep 986411 = 1479617) B1479617
theorem B986423 : Blo 984595 986423 := bstep (se 1 (by rfl) ⟨739817, by rfl⟩ : syracuseStep 986423 = 1479635) B1479635
theorem B986443 : Blo 984595 986443 := bstep (se 1 (by rfl) ⟨739832, by rfl⟩ : syracuseStep 986443 = 1479665) B1479665
theorem B1871191 : Blo 984595 1871191 := bstep (se 1 (by rfl) ⟨1403393, by rfl⟩ : syracuseStep 1871191 = 2806787) B2806787
theorem B986455 : Blo 984595 986455 := bstep (se 1 (by rfl) ⟨739841, by rfl⟩ : syracuseStep 986455 = 1479683) B1479683
theorem B986475 : Blo 984595 986475 := bstep (se 1 (by rfl) ⟨739856, by rfl⟩ : syracuseStep 986475 = 1479713) B1479713
theorem B986487 : Blo 984595 986487 := bstep (se 1 (by rfl) ⟨739865, by rfl⟩ : syracuseStep 986487 = 1479731) B1479731
theorem B1478027 : Blo 984595 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B986507 : Blo 984595 986507 := bstep (se 1 (by rfl) ⟨739880, by rfl⟩ : syracuseStep 986507 = 1479761) B1479761
theorem B1478039 : Blo 984595 1478039 := bstep (se 1 (by rfl) ⟨1108529, by rfl⟩ : syracuseStep 1478039 = 2217059) B2217059
theorem B986519 : Blo 984595 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B986539 : Blo 984595 986539 := bstep (se 1 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 986539 = 1479809) B1479809
theorem B986551 : Blo 984595 986551 := bstep (se 1 (by rfl) ⟨739913, by rfl⟩ : syracuseStep 986551 = 1479827) B1479827
theorem B2493899 : Blo 984595 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B986571 : Blo 984595 986571 := bstep (se 1 (by rfl) ⟨739928, by rfl⟩ : syracuseStep 986571 = 1479857) B1479857
theorem B986583 : Blo 984595 986583 := bstep (se 1 (by rfl) ⟨739937, by rfl⟩ : syracuseStep 986583 = 1479875) B1479875
theorem B1478105 : Blo 984595 1478105 := bstep (se 2 (by rfl) ⟨554289, by rfl⟩ : syracuseStep 1478105 = 1108579) B1108579
theorem B986603 : Blo 984595 986603 := bstep (se 1 (by rfl) ⟨739952, by rfl⟩ : syracuseStep 986603 = 1479905) B1479905
theorem B986615 : Blo 984595 986615 := bstep (se 1 (by rfl) ⟨739961, by rfl⟩ : syracuseStep 986615 = 1479923) B1479923
theorem B986635 : Blo 984595 986635 := bstep (se 1 (by rfl) ⟨739976, by rfl⟩ : syracuseStep 986635 = 1479953) B1479953
theorem B986647 : Blo 984595 986647 := bstep (se 1 (by rfl) ⟨739985, by rfl⟩ : syracuseStep 986647 = 1479971) B1479971
theorem B986667 : Blo 984595 986667 := bstep (se 1 (by rfl) ⟨740000, by rfl⟩ : syracuseStep 986667 = 1480001) B1480001
theorem B986679 : Blo 984595 986679 := bstep (se 1 (by rfl) ⟨740009, by rfl⟩ : syracuseStep 986679 = 1480019) B1480019
theorem B1478219 : Blo 984595 1478219 := bstep (se 1 (by rfl) ⟨1108664, by rfl⟩ : syracuseStep 1478219 = 2217329) B2217329
theorem B986699 : Blo 984595 986699 := bstep (se 1 (by rfl) ⟨740024, by rfl⟩ : syracuseStep 986699 = 1480049) B1480049
theorem B1478231 : Blo 984595 1478231 := bstep (se 1 (by rfl) ⟨1108673, by rfl⟩ : syracuseStep 1478231 = 2217347) B2217347
theorem B986711 : Blo 984595 986711 := bstep (se 1 (by rfl) ⟨740033, by rfl⟩ : syracuseStep 986711 = 1480067) B1480067
theorem B986731 : Blo 984595 986731 := bstep (se 1 (by rfl) ⟨740048, by rfl⟩ : syracuseStep 986731 = 1480097) B1480097
theorem B986743 : Blo 984595 986743 := bstep (se 1 (by rfl) ⟨740057, by rfl⟩ : syracuseStep 986743 = 1480115) B1480115
theorem B986763 : Blo 984595 986763 := bstep (se 1 (by rfl) ⟨740072, by rfl⟩ : syracuseStep 986763 = 1480145) B1480145
theorem B2002571 : Blo 984595 2002571 := bstep (se 1 (by rfl) ⟨1501928, by rfl⟩ : syracuseStep 2002571 = 3003857) B3003857
theorem B986775 : Blo 984595 986775 := bstep (se 1 (by rfl) ⟨740081, by rfl⟩ : syracuseStep 986775 = 1480163) B1480163
theorem B1478297 : Blo 984595 1478297 := bstep (se 2 (by rfl) ⟨554361, by rfl⟩ : syracuseStep 1478297 = 1108723) B1108723
theorem B986795 : Blo 984595 986795 := bstep (se 1 (by rfl) ⟨740096, by rfl⟩ : syracuseStep 986795 = 1480193) B1480193
theorem B4492979 : Blo 984595 4492979 := bstep (se 1 (by rfl) ⟨3369734, by rfl⟩ : syracuseStep 4492979 = 6739469) B6739469
theorem B986807 : Blo 984595 986807 := bstep (se 1 (by rfl) ⟨740105, by rfl⟩ : syracuseStep 986807 = 1480211) B1480211
theorem B2133707 : Blo 984595 2133707 := bstep (se 1 (by rfl) ⟨1600280, by rfl⟩ : syracuseStep 2133707 = 3200561) B3200561
theorem B986827 : Blo 984595 986827 := bstep (se 1 (by rfl) ⟨740120, by rfl⟩ : syracuseStep 986827 = 1480241) B1480241
theorem B986839 : Blo 984595 986839 := bstep (se 1 (by rfl) ⟨740129, by rfl⟩ : syracuseStep 986839 = 1480259) B1480259
theorem B3378905 : Blo 984595 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B986859 : Blo 984595 986859 := bstep (se 1 (by rfl) ⟨740144, by rfl⟩ : syracuseStep 986859 = 1480289) B1480289
theorem B986871 : Blo 984595 986871 := bstep (se 1 (by rfl) ⟨740153, by rfl⟩ : syracuseStep 986871 = 1480307) B1480307
theorem B1478411 : Blo 984595 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B986891 : Blo 984595 986891 := bstep (se 1 (by rfl) ⟨740168, by rfl⟩ : syracuseStep 986891 = 1480337) B1480337
theorem B1478423 : Blo 984595 1478423 := bstep (se 1 (by rfl) ⟨1108817, by rfl⟩ : syracuseStep 1478423 = 2217635) B2217635
theorem B986903 : Blo 984595 986903 := bstep (se 1 (by rfl) ⟨740177, by rfl⟩ : syracuseStep 986903 = 1480355) B1480355
theorem B986923 : Blo 984595 986923 := bstep (se 1 (by rfl) ⟨740192, by rfl⟩ : syracuseStep 986923 = 1480385) B1480385
theorem B986935 : Blo 984595 986935 := bstep (se 1 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 986935 = 1480403) B1480403
theorem B2494273 : Blo 984595 2494273 := bstep (se 2 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 2494273 = 1870705) B1870705
theorem B986955 : Blo 984595 986955 := bstep (se 1 (by rfl) ⟨740216, by rfl⟩ : syracuseStep 986955 = 1480433) B1480433
theorem B1249111 : Blo 984595 1249111 := bstep (se 1 (by rfl) ⟨936833, by rfl⟩ : syracuseStep 1249111 = 1873667) B1873667
theorem B986967 : Blo 984595 986967 := bstep (se 1 (by rfl) ⟨740225, by rfl⟩ : syracuseStep 986967 = 1480451) B1480451
theorem B1478489 : Blo 984595 1478489 := bstep (se 2 (by rfl) ⟨554433, by rfl⟩ : syracuseStep 1478489 = 1108867) B1108867
theorem B986987 : Blo 984595 986987 := bstep (se 1 (by rfl) ⟨740240, by rfl⟩ : syracuseStep 986987 = 1480481) B1480481
theorem B986999 : Blo 984595 986999 := bstep (se 1 (by rfl) ⟨740249, by rfl⟩ : syracuseStep 986999 = 1480499) B1480499
theorem B987019 : Blo 984595 987019 := bstep (se 1 (by rfl) ⟨740264, by rfl⟩ : syracuseStep 987019 = 1480529) B1480529
theorem B987031 : Blo 984595 987031 := bstep (se 1 (by rfl) ⟨740273, by rfl⟩ : syracuseStep 987031 = 1480547) B1480547
theorem B987051 : Blo 984595 987051 := bstep (se 1 (by rfl) ⟨740288, by rfl⟩ : syracuseStep 987051 = 1480577) B1480577
theorem B987063 : Blo 984595 987063 := bstep (se 1 (by rfl) ⟨740297, by rfl⟩ : syracuseStep 987063 = 1480595) B1480595
theorem B1183691 : Blo 984595 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B1478603 : Blo 984595 1478603 := bstep (se 1 (by rfl) ⟨1108952, by rfl⟩ : syracuseStep 1478603 = 2217905) B2217905
theorem B987083 : Blo 984595 987083 := bstep (se 1 (by rfl) ⟨740312, by rfl⟩ : syracuseStep 987083 = 1480625) B1480625
theorem B1478615 : Blo 984595 1478615 := bstep (se 1 (by rfl) ⟨1108961, by rfl⟩ : syracuseStep 1478615 = 2217923) B2217923
theorem B987095 : Blo 984595 987095 := bstep (se 1 (by rfl) ⟨740321, by rfl⟩ : syracuseStep 987095 = 1480643) B1480643
theorem B987115 : Blo 984595 987115 := bstep (se 1 (by rfl) ⟨740336, by rfl⟩ : syracuseStep 987115 = 1480673) B1480673
theorem B987127 : Blo 984595 987127 := bstep (se 1 (by rfl) ⟨740345, by rfl⟩ : syracuseStep 987127 = 1480691) B1480691
theorem B987147 : Blo 984595 987147 := bstep (se 1 (by rfl) ⟨740360, by rfl⟩ : syracuseStep 987147 = 1480721) B1480721
theorem B987159 : Blo 984595 987159 := bstep (se 1 (by rfl) ⟨740369, by rfl⟩ : syracuseStep 987159 = 1480739) B1480739
theorem B1478681 : Blo 984595 1478681 := bstep (se 2 (by rfl) ⟨554505, by rfl⟩ : syracuseStep 1478681 = 1109011) B1109011
theorem B987179 : Blo 984595 987179 := bstep (se 1 (by rfl) ⟨740384, by rfl⟩ : syracuseStep 987179 = 1480769) B1480769
theorem B987191 : Blo 984595 987191 := bstep (se 1 (by rfl) ⟨740393, by rfl⟩ : syracuseStep 987191 = 1480787) B1480787
theorem B987211 : Blo 984595 987211 := bstep (se 1 (by rfl) ⟨740408, by rfl⟩ : syracuseStep 987211 = 1480817) B1480817
theorem B987223 : Blo 984595 987223 := bstep (se 1 (by rfl) ⟨740417, by rfl⟩ : syracuseStep 987223 = 1480835) B1480835
theorem B987243 : Blo 984595 987243 := bstep (se 1 (by rfl) ⟨740432, by rfl⟩ : syracuseStep 987243 = 1480865) B1480865
theorem B987255 : Blo 984595 987255 := bstep (se 1 (by rfl) ⟨740441, by rfl⟩ : syracuseStep 987255 = 1480883) B1480883
theorem B1478795 : Blo 984595 1478795 := bstep (se 1 (by rfl) ⟨1109096, by rfl⟩ : syracuseStep 1478795 = 2218193) B2218193
theorem B1872011 : Blo 984595 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B987275 : Blo 984595 987275 := bstep (se 1 (by rfl) ⟨740456, by rfl⟩ : syracuseStep 987275 = 1480913) B1480913
theorem B1478807 : Blo 984595 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B987287 : Blo 984595 987287 := bstep (se 1 (by rfl) ⟨740465, by rfl⟩ : syracuseStep 987287 = 1480931) B1480931
theorem B987307 : Blo 984595 987307 := bstep (se 1 (by rfl) ⟨740480, by rfl⟩ : syracuseStep 987307 = 1480961) B1480961
theorem B987319 : Blo 984595 987319 := bstep (se 1 (by rfl) ⟨740489, by rfl⟩ : syracuseStep 987319 = 1480979) B1480979
theorem B1872065 : Blo 984595 1872065 := bstep (se 2 (by rfl) ⟨702024, by rfl⟩ : syracuseStep 1872065 = 1404049) B1404049
theorem B987339 : Blo 984595 987339 := bstep (se 1 (by rfl) ⟨740504, by rfl⟩ : syracuseStep 987339 = 1481009) B1481009
theorem B1052887 : Blo 984595 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B987351 : Blo 984595 987351 := bstep (se 1 (by rfl) ⟨740513, by rfl⟩ : syracuseStep 987351 = 1481027) B1481027
theorem B1478873 : Blo 984595 1478873 := bstep (se 2 (by rfl) ⟨554577, by rfl⟩ : syracuseStep 1478873 = 1109155) B1109155
theorem B987371 : Blo 984595 987371 := bstep (se 1 (by rfl) ⟨740528, by rfl⟩ : syracuseStep 987371 = 1481057) B1481057
theorem B987383 : Blo 984595 987383 := bstep (se 1 (by rfl) ⟨740537, by rfl⟩ : syracuseStep 987383 = 1481075) B1481075
theorem B987403 : Blo 984595 987403 := bstep (se 1 (by rfl) ⟨740552, by rfl⟩ : syracuseStep 987403 = 1481105) B1481105
theorem B987415 : Blo 984595 987415 := bstep (se 1 (by rfl) ⟨740561, by rfl⟩ : syracuseStep 987415 = 1481123) B1481123
theorem B987435 : Blo 984595 987435 := bstep (se 1 (by rfl) ⟨740576, by rfl⟩ : syracuseStep 987435 = 1481153) B1481153
theorem B68227373 : Blo 984595 68227373 := bstep (se 3 (by rfl) ⟨12792632, by rfl⟩ : syracuseStep 68227373 = 25585265) B25585265
theorem B987447 : Blo 984595 987447 := bstep (se 1 (by rfl) ⟨740585, by rfl⟩ : syracuseStep 987447 = 1481171) B1481171
theorem B1478987 : Blo 984595 1478987 := bstep (se 1 (by rfl) ⟨1109240, by rfl⟩ : syracuseStep 1478987 = 2218481) B2218481
theorem B987467 : Blo 984595 987467 := bstep (se 1 (by rfl) ⟨740600, by rfl⟩ : syracuseStep 987467 = 1481201) B1481201
theorem B1478999 : Blo 984595 1478999 := bstep (se 1 (by rfl) ⟨1109249, by rfl⟩ : syracuseStep 1478999 = 2218499) B2218499
theorem B987479 : Blo 984595 987479 := bstep (se 1 (by rfl) ⟨740609, by rfl⟩ : syracuseStep 987479 = 1481219) B1481219
theorem B987499 : Blo 984595 987499 := bstep (se 1 (by rfl) ⟨740624, by rfl⟩ : syracuseStep 987499 = 1481249) B1481249
theorem B987511 : Blo 984595 987511 := bstep (se 1 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 987511 = 1481267) B1481267
theorem B987531 : Blo 984595 987531 := bstep (se 1 (by rfl) ⟨740648, by rfl⟩ : syracuseStep 987531 = 1481297) B1481297
theorem B2494871 : Blo 984595 2494871 := bstep (se 1 (by rfl) ⟨1871153, by rfl⟩ : syracuseStep 2494871 = 3742307) B3742307
theorem B987543 : Blo 984595 987543 := bstep (se 1 (by rfl) ⟨740657, by rfl⟩ : syracuseStep 987543 = 1481315) B1481315
theorem B1479065 : Blo 984595 1479065 := bstep (se 2 (by rfl) ⟨554649, by rfl⟩ : syracuseStep 1479065 = 1109299) B1109299
theorem B987563 : Blo 984595 987563 := bstep (se 1 (by rfl) ⟨740672, by rfl⟩ : syracuseStep 987563 = 1481345) B1481345
theorem B9015731 : Blo 984595 9015731 := bstep (se 1 (by rfl) ⟨6761798, by rfl⟩ : syracuseStep 9015731 = 13523597) B13523597
theorem B987575 : Blo 984595 987575 := bstep (se 1 (by rfl) ⟨740681, by rfl⟩ : syracuseStep 987575 = 1481363) B1481363
theorem B987595 : Blo 984595 987595 := bstep (se 1 (by rfl) ⟨740696, by rfl⟩ : syracuseStep 987595 = 1481393) B1481393
theorem B987607 : Blo 984595 987607 := bstep (se 1 (by rfl) ⟨740705, by rfl⟩ : syracuseStep 987607 = 1481411) B1481411
theorem B987627 : Blo 984595 987627 := bstep (se 1 (by rfl) ⟨740720, by rfl⟩ : syracuseStep 987627 = 1481441) B1481441
theorem B987639 : Blo 984595 987639 := bstep (se 1 (by rfl) ⟨740729, by rfl⟩ : syracuseStep 987639 = 1481459) B1481459
theorem B1479179 : Blo 984595 1479179 := bstep (se 1 (by rfl) ⟨1109384, by rfl⟩ : syracuseStep 1479179 = 2218769) B2218769
theorem B987659 : Blo 984595 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B1479191 : Blo 984595 1479191 := bstep (se 1 (by rfl) ⟨1109393, by rfl⟩ : syracuseStep 1479191 = 2218787) B2218787
theorem B987671 : Blo 984595 987671 := bstep (se 1 (by rfl) ⟨740753, by rfl⟩ : syracuseStep 987671 = 1481507) B1481507
theorem B987691 : Blo 984595 987691 := bstep (se 1 (by rfl) ⟨740768, by rfl⟩ : syracuseStep 987691 = 1481537) B1481537
theorem B987703 : Blo 984595 987703 := bstep (se 1 (by rfl) ⟨740777, by rfl⟩ : syracuseStep 987703 = 1481555) B1481555
theorem B987723 : Blo 984595 987723 := bstep (se 1 (by rfl) ⟨740792, by rfl⟩ : syracuseStep 987723 = 1481585) B1481585
theorem B987735 : Blo 984595 987735 := bstep (se 1 (by rfl) ⟨740801, by rfl⟩ : syracuseStep 987735 = 1481603) B1481603
theorem B1479257 : Blo 984595 1479257 := bstep (se 2 (by rfl) ⟨554721, by rfl⟩ : syracuseStep 1479257 = 1109443) B1109443
theorem B4264541 : Blo 984595 4264541 := bstep (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) B1599203
theorem B987755 : Blo 984595 987755 := bstep (se 1 (by rfl) ⟨740816, by rfl⟩ : syracuseStep 987755 = 1481633) B1481633
theorem B987767 : Blo 984595 987767 := bstep (se 1 (by rfl) ⟨740825, by rfl⟩ : syracuseStep 987767 = 1481651) B1481651
theorem B1249931 : Blo 984595 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B987787 : Blo 984595 987787 := bstep (se 1 (by rfl) ⟨740840, by rfl⟩ : syracuseStep 987787 = 1481681) B1481681
theorem B987799 : Blo 984595 987799 := bstep (se 1 (by rfl) ⟨740849, by rfl⟩ : syracuseStep 987799 = 1481699) B1481699
theorem B2003609 : Blo 984595 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B987819 : Blo 984595 987819 := bstep (se 1 (by rfl) ⟨740864, by rfl⟩ : syracuseStep 987819 = 1481729) B1481729
theorem B987831 : Blo 984595 987831 := bstep (se 1 (by rfl) ⟨740873, by rfl⟩ : syracuseStep 987831 = 1481747) B1481747
theorem B3740363 : Blo 984595 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B1479371 : Blo 984595 1479371 := bstep (se 1 (by rfl) ⟨1109528, by rfl⟩ : syracuseStep 1479371 = 2219057) B2219057
theorem B987851 : Blo 984595 987851 := bstep (se 1 (by rfl) ⟨740888, by rfl⟩ : syracuseStep 987851 = 1481777) B1481777
theorem B3379915 : Blo 984595 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B1479383 : Blo 984595 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B987863 : Blo 984595 987863 := bstep (se 1 (by rfl) ⟨740897, by rfl⟩ : syracuseStep 987863 = 1481795) B1481795
theorem B3740377 : Blo 984595 3740377 := bstep (se 2 (by rfl) ⟨1402641, by rfl⟩ : syracuseStep 3740377 = 2805283) B2805283
theorem B987883 : Blo 984595 987883 := bstep (se 1 (by rfl) ⟨740912, by rfl⟩ : syracuseStep 987883 = 1481825) B1481825
theorem B987895 : Blo 984595 987895 := bstep (se 1 (by rfl) ⟨740921, by rfl⟩ : syracuseStep 987895 = 1481843) B1481843
theorem B987915 : Blo 984595 987915 := bstep (se 1 (by rfl) ⟨740936, by rfl⟩ : syracuseStep 987915 = 1481873) B1481873
theorem B987927 : Blo 984595 987927 := bstep (se 1 (by rfl) ⟨740945, by rfl⟩ : syracuseStep 987927 = 1481891) B1481891
theorem B1479449 : Blo 984595 1479449 := bstep (se 2 (by rfl) ⟨554793, by rfl⟩ : syracuseStep 1479449 = 1109587) B1109587
theorem B987947 : Blo 984595 987947 := bstep (se 1 (by rfl) ⟨740960, by rfl⟩ : syracuseStep 987947 = 1481921) B1481921
theorem B987959 : Blo 984595 987959 := bstep (se 1 (by rfl) ⟨740969, by rfl⟩ : syracuseStep 987959 = 1481939) B1481939
theorem B4494145 : Blo 984595 4494145 := bstep (se 2 (by rfl) ⟨1685304, by rfl⟩ : syracuseStep 4494145 = 3370609) B3370609
theorem B987979 : Blo 984595 987979 := bstep (se 1 (by rfl) ⟨740984, by rfl⟩ : syracuseStep 987979 = 1481969) B1481969
theorem B987991 : Blo 984595 987991 := bstep (se 1 (by rfl) ⟨740993, by rfl⟩ : syracuseStep 987991 = 1481987) B1481987
theorem B27005795 : Blo 984595 27005795 := bstep (se 1 (by rfl) ⟨20254346, by rfl⟩ : syracuseStep 27005795 = 40508693) B40508693
theorem B988011 : Blo 984595 988011 := bstep (se 1 (by rfl) ⟨741008, by rfl⟩ : syracuseStep 988011 = 1482017) B1482017
theorem B988023 : Blo 984595 988023 := bstep (se 1 (by rfl) ⟨741017, by rfl⟩ : syracuseStep 988023 = 1482035) B1482035
theorem B1479563 : Blo 984595 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B988043 : Blo 984595 988043 := bstep (se 1 (by rfl) ⟨741032, by rfl⟩ : syracuseStep 988043 = 1482065) B1482065
theorem B1479575 : Blo 984595 1479575 := bstep (se 1 (by rfl) ⟨1109681, by rfl⟩ : syracuseStep 1479575 = 2219363) B2219363
theorem B988055 : Blo 984595 988055 := bstep (se 1 (by rfl) ⟨741041, by rfl⟩ : syracuseStep 988055 = 1482083) B1482083
theorem B988075 : Blo 984595 988075 := bstep (se 1 (by rfl) ⟨741056, by rfl⟩ : syracuseStep 988075 = 1482113) B1482113
theorem B988087 : Blo 984595 988087 := bstep (se 1 (by rfl) ⟨741065, by rfl⟩ : syracuseStep 988087 = 1482131) B1482131
theorem B988107 : Blo 984595 988107 := bstep (se 1 (by rfl) ⟨741080, by rfl⟩ : syracuseStep 988107 = 1482161) B1482161
theorem B988119 : Blo 984595 988119 := bstep (se 1 (by rfl) ⟨741089, by rfl⟩ : syracuseStep 988119 = 1482179) B1482179
theorem B1479641 : Blo 984595 1479641 := bstep (se 2 (by rfl) ⟨554865, by rfl⟩ : syracuseStep 1479641 = 1109731) B1109731
theorem B988139 : Blo 984595 988139 := bstep (se 1 (by rfl) ⟨741104, by rfl⟩ : syracuseStep 988139 = 1482209) B1482209
theorem B988151 : Blo 984595 988151 := bstep (se 1 (by rfl) ⟨741113, by rfl⟩ : syracuseStep 988151 = 1482227) B1482227
theorem B2135041 : Blo 984595 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1053707 : Blo 984595 1053707 := bstep (se 1 (by rfl) ⟨790280, by rfl⟩ : syracuseStep 1053707 = 1580561) B1580561
theorem B988171 : Blo 984595 988171 := bstep (se 1 (by rfl) ⟨741128, by rfl⟩ : syracuseStep 988171 = 1482257) B1482257
theorem B4985873 : Blo 984595 4985873 := bstep (se 2 (by rfl) ⟨1869702, by rfl⟩ : syracuseStep 4985873 = 3739405) B3739405
theorem B988183 : Blo 984595 988183 := bstep (se 1 (by rfl) ⟨741137, by rfl⟩ : syracuseStep 988183 = 1482275) B1482275
theorem B988203 : Blo 984595 988203 := bstep (se 1 (by rfl) ⟨741152, by rfl⟩ : syracuseStep 988203 = 1482305) B1482305
theorem B988215 : Blo 984595 988215 := bstep (se 1 (by rfl) ⟨741161, by rfl⟩ : syracuseStep 988215 = 1482323) B1482323
theorem B1774657 : Blo 984595 1774657 := bstep (se 2 (by rfl) ⟨665496, by rfl⟩ : syracuseStep 1774657 = 1330993) B1330993
theorem B1479755 : Blo 984595 1479755 := bstep (se 1 (by rfl) ⟨1109816, by rfl⟩ : syracuseStep 1479755 = 2219633) B2219633
theorem B988235 : Blo 984595 988235 := bstep (se 1 (by rfl) ⟨741176, by rfl⟩ : syracuseStep 988235 = 1482353) B1482353
theorem B1479767 : Blo 984595 1479767 := bstep (se 1 (by rfl) ⟨1109825, by rfl⟩ : syracuseStep 1479767 = 2219651) B2219651
theorem B1872983 : Blo 984595 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B988247 : Blo 984595 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B988267 : Blo 984595 988267 := bstep (se 1 (by rfl) ⟨741200, by rfl⟩ : syracuseStep 988267 = 1482401) B1482401
theorem B988279 : Blo 984595 988279 := bstep (se 1 (by rfl) ⟨741209, by rfl⟩ : syracuseStep 988279 = 1482419) B1482419
theorem B988299 : Blo 984595 988299 := bstep (se 1 (by rfl) ⟨741224, by rfl⟩ : syracuseStep 988299 = 1482449) B1482449
theorem B988311 : Blo 984595 988311 := bstep (se 1 (by rfl) ⟨741233, by rfl⟩ : syracuseStep 988311 = 1482467) B1482467
theorem B1479833 : Blo 984595 1479833 := bstep (se 2 (by rfl) ⟨554937, by rfl⟩ : syracuseStep 1479833 = 1109875) B1109875
theorem B988331 : Blo 984595 988331 := bstep (se 1 (by rfl) ⟨741248, by rfl⟩ : syracuseStep 988331 = 1482497) B1482497
theorem B4986035 : Blo 984595 4986035 := bstep (se 1 (by rfl) ⟨3739526, by rfl⟩ : syracuseStep 4986035 = 7479053) B7479053
theorem B6755507 : Blo 984595 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B988343 : Blo 984595 988343 := bstep (se 1 (by rfl) ⟨741257, by rfl⟩ : syracuseStep 988343 = 1482515) B1482515
theorem B2495681 : Blo 984595 2495681 := bstep (se 2 (by rfl) ⟨935880, by rfl⟩ : syracuseStep 2495681 = 1871761) B1871761
theorem B988363 : Blo 984595 988363 := bstep (se 1 (by rfl) ⟨741272, by rfl⟩ : syracuseStep 988363 = 1482545) B1482545
theorem B988375 : Blo 984595 988375 := bstep (se 1 (by rfl) ⟨741281, by rfl⟩ : syracuseStep 988375 = 1482563) B1482563
theorem B988395 : Blo 984595 988395 := bstep (se 1 (by rfl) ⟨741296, by rfl⟩ : syracuseStep 988395 = 1482593) B1482593
theorem B988407 : Blo 984595 988407 := bstep (se 1 (by rfl) ⟨741305, by rfl⟩ : syracuseStep 988407 = 1482611) B1482611
theorem B1479947 : Blo 984595 1479947 := bstep (se 1 (by rfl) ⟨1109960, by rfl⟩ : syracuseStep 1479947 = 2219921) B2219921
theorem B988427 : Blo 984595 988427 := bstep (se 1 (by rfl) ⟨741320, by rfl⟩ : syracuseStep 988427 = 1482641) B1482641
theorem B1479959 : Blo 984595 1479959 := bstep (se 1 (by rfl) ⟨1109969, by rfl⟩ : syracuseStep 1479959 = 2219939) B2219939
theorem B988439 : Blo 984595 988439 := bstep (se 1 (by rfl) ⟨741329, by rfl⟩ : syracuseStep 988439 = 1482659) B1482659
theorem B988459 : Blo 984595 988459 := bstep (se 1 (by rfl) ⟨741344, by rfl⟩ : syracuseStep 988459 = 1482689) B1482689
theorem B988471 : Blo 984595 988471 := bstep (se 1 (by rfl) ⟨741353, by rfl⟩ : syracuseStep 988471 = 1482707) B1482707
theorem B1250635 : Blo 984595 1250635 := bstep (se 1 (by rfl) ⟨937976, by rfl⟩ : syracuseStep 1250635 = 1875953) B1875953
theorem B988491 : Blo 984595 988491 := bstep (se 1 (by rfl) ⟨741368, by rfl⟩ : syracuseStep 988491 = 1482737) B1482737
theorem B988503 : Blo 984595 988503 := bstep (se 1 (by rfl) ⟨741377, by rfl⟩ : syracuseStep 988503 = 1482755) B1482755
theorem B1480025 : Blo 984595 1480025 := bstep (se 2 (by rfl) ⟨555009, by rfl⟩ : syracuseStep 1480025 = 1110019) B1110019
theorem B988523 : Blo 984595 988523 := bstep (se 1 (by rfl) ⟨741392, by rfl⟩ : syracuseStep 988523 = 1482785) B1482785
theorem B988535 : Blo 984595 988535 := bstep (se 1 (by rfl) ⟨741401, by rfl⟩ : syracuseStep 988535 = 1482803) B1482803
theorem B5608835 : Blo 984595 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B988555 : Blo 984595 988555 := bstep (se 1 (by rfl) ⟨741416, by rfl⟩ : syracuseStep 988555 = 1482833) B1482833
theorem B988567 : Blo 984595 988567 := bstep (se 1 (by rfl) ⟨741425, by rfl⟩ : syracuseStep 988567 = 1482851) B1482851
theorem B988587 : Blo 984595 988587 := bstep (se 1 (by rfl) ⟨741440, by rfl⟩ : syracuseStep 988587 = 1482881) B1482881
theorem B1480139 : Blo 984595 1480139 := bstep (se 1 (by rfl) ⟨1110104, by rfl⟩ : syracuseStep 1480139 = 2220209) B2220209
theorem B1480151 : Blo 984595 1480151 := bstep (se 1 (by rfl) ⟨1110113, by rfl⟩ : syracuseStep 1480151 = 2220227) B2220227
theorem B1480217 : Blo 984595 1480217 := bstep (se 2 (by rfl) ⟨555081, by rfl⟩ : syracuseStep 1480217 = 1110163) B1110163
theorem B10688075 : Blo 984595 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B1250903 : Blo 984595 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B1873523 : Blo 984595 1873523 := bstep (se 1 (by rfl) ⟨1405142, by rfl⟩ : syracuseStep 1873523 = 2810285) B2810285
theorem B1480331 : Blo 984595 1480331 := bstep (se 1 (by rfl) ⟨1110248, by rfl⟩ : syracuseStep 1480331 = 2220497) B2220497
theorem B3741335 : Blo 984595 3741335 := bstep (se 1 (by rfl) ⟨2806001, by rfl⟩ : syracuseStep 3741335 = 5612003) B5612003
theorem B1480343 : Blo 984595 1480343 := bstep (se 1 (by rfl) ⟨1110257, by rfl⟩ : syracuseStep 1480343 = 2220515) B2220515
theorem B2496217 : Blo 984595 2496217 := bstep (se 2 (by rfl) ⟨936081, by rfl⟩ : syracuseStep 2496217 = 1872163) B1872163
theorem B1480409 : Blo 984595 1480409 := bstep (se 2 (by rfl) ⟨555153, by rfl⟩ : syracuseStep 1480409 = 1110307) B1110307
theorem B1480523 : Blo 984595 1480523 := bstep (se 1 (by rfl) ⟨1110392, by rfl⟩ : syracuseStep 1480523 = 2220785) B2220785
theorem B7116619 : Blo 984595 7116619 := bstep (se 1 (by rfl) ⟨5337464, by rfl⟩ : syracuseStep 7116619 = 10674929) B10674929
theorem B1480535 : Blo 984595 1480535 := bstep (se 1 (by rfl) ⟨1110401, by rfl⟩ : syracuseStep 1480535 = 2220803) B2220803
theorem B1480601 : Blo 984595 1480601 := bstep (se 2 (by rfl) ⟨555225, by rfl⟩ : syracuseStep 1480601 = 1110451) B1110451
theorem B4495277 : Blo 984595 4495277 := bstep (se 3 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 4495277 = 1685729) B1685729
theorem B11409329 : Blo 984595 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B1054711 : Blo 984595 1054711 := bstep (se 1 (by rfl) ⟨791033, by rfl⟩ : syracuseStep 1054711 = 1582067) B1582067
theorem B1480715 : Blo 984595 1480715 := bstep (se 1 (by rfl) ⟨1110536, by rfl⟩ : syracuseStep 1480715 = 2221073) B2221073
theorem B1480727 : Blo 984595 1480727 := bstep (se 1 (by rfl) ⟨1110545, by rfl⟩ : syracuseStep 1480727 = 2221091) B2221091
theorem B1874009 : Blo 984595 1874009 := bstep (se 2 (by rfl) ⟨702753, by rfl⟩ : syracuseStep 1874009 = 1405507) B1405507
theorem B1480793 : Blo 984595 1480793 := bstep (se 2 (by rfl) ⟨555297, by rfl⟩ : syracuseStep 1480793 = 1110595) B1110595
theorem B1480907 : Blo 984595 1480907 := bstep (se 1 (by rfl) ⟨1110680, by rfl⟩ : syracuseStep 1480907 = 2221361) B2221361
theorem B1480919 : Blo 984595 1480919 := bstep (se 1 (by rfl) ⟨1110689, by rfl⟩ : syracuseStep 1480919 = 2221379) B2221379
theorem B1480985 : Blo 984595 1480985 := bstep (se 2 (by rfl) ⟨555369, by rfl⟩ : syracuseStep 1480985 = 1110739) B1110739
theorem B1481099 : Blo 984595 1481099 := bstep (se 1 (by rfl) ⟨1110824, by rfl⟩ : syracuseStep 1481099 = 2221649) B2221649
theorem B1481111 : Blo 984595 1481111 := bstep (se 1 (by rfl) ⟨1110833, by rfl⟩ : syracuseStep 1481111 = 2221667) B2221667
theorem B1481177 : Blo 984595 1481177 := bstep (se 2 (by rfl) ⟨555441, by rfl⟩ : syracuseStep 1481177 = 1110883) B1110883
theorem B2366027 : Blo 984595 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B1481291 : Blo 984595 1481291 := bstep (se 1 (by rfl) ⟨1110968, by rfl⟩ : syracuseStep 1481291 = 2221937) B2221937
theorem B6330955 : Blo 984595 6330955 := bstep (se 1 (by rfl) ⟨4748216, by rfl⟩ : syracuseStep 6330955 = 9496433) B9496433
theorem B1481303 : Blo 984595 1481303 := bstep (se 1 (by rfl) ⟨1110977, by rfl⟩ : syracuseStep 1481303 = 2221955) B2221955
theorem B5053079 : Blo 984595 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B1481369 : Blo 984595 1481369 := bstep (se 2 (by rfl) ⟨555513, by rfl⟩ : syracuseStep 1481369 = 1111027) B1111027
theorem B1055467 : Blo 984595 1055467 := bstep (se 1 (by rfl) ⟨791600, by rfl⟩ : syracuseStep 1055467 = 1583201) B1583201
theorem B1481483 : Blo 984595 1481483 := bstep (se 1 (by rfl) ⟨1111112, by rfl⟩ : syracuseStep 1481483 = 2222225) B2222225
theorem B1481495 : Blo 984595 1481495 := bstep (se 1 (by rfl) ⟨1111121, by rfl⟩ : syracuseStep 1481495 = 2222243) B2222243
theorem B2497331 : Blo 984595 2497331 := bstep (se 1 (by rfl) ⟨1872998, by rfl⟩ : syracuseStep 2497331 = 3745997) B3745997
theorem B7478081 : Blo 984595 7478081 := bstep (se 2 (by rfl) ⟨2804280, by rfl⟩ : syracuseStep 7478081 = 5608561) B5608561
theorem B1481561 : Blo 984595 1481561 := bstep (se 2 (by rfl) ⟨555585, by rfl⟩ : syracuseStep 1481561 = 1111171) B1111171
theorem B3742595 : Blo 984595 3742595 := bstep (se 1 (by rfl) ⟨2806946, by rfl⟩ : syracuseStep 3742595 = 5613893) B5613893
theorem B1481675 : Blo 984595 1481675 := bstep (se 1 (by rfl) ⟨1111256, by rfl⟩ : syracuseStep 1481675 = 2222513) B2222513
theorem B1481687 : Blo 984595 1481687 := bstep (se 1 (by rfl) ⟨1111265, by rfl⟩ : syracuseStep 1481687 = 2222531) B2222531
theorem B1481753 : Blo 984595 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B4987979 : Blo 984595 4987979 := bstep (se 1 (by rfl) ⟨3740984, by rfl⟩ : syracuseStep 4987979 = 7481969) B7481969
theorem B2497625 : Blo 984595 2497625 := bstep (se 2 (by rfl) ⟨936609, by rfl⟩ : syracuseStep 2497625 = 1873219) B1873219
theorem B1481867 : Blo 984595 1481867 := bstep (se 1 (by rfl) ⟨1111400, by rfl⟩ : syracuseStep 1481867 = 2222801) B2222801
theorem B1481879 : Blo 984595 1481879 := bstep (se 1 (by rfl) ⟨1111409, by rfl⟩ : syracuseStep 1481879 = 2222819) B2222819
theorem B8101043 : Blo 984595 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B6331571 : Blo 984595 6331571 := bstep (se 1 (by rfl) ⟨4748678, by rfl⟩ : syracuseStep 6331571 = 9497357) B9497357
theorem B1481945 : Blo 984595 1481945 := bstep (se 2 (by rfl) ⟨555729, by rfl⟩ : syracuseStep 1481945 = 1111459) B1111459
theorem B1482059 : Blo 984595 1482059 := bstep (se 1 (by rfl) ⟨1111544, by rfl⟩ : syracuseStep 1482059 = 2223089) B2223089
theorem B1482071 : Blo 984595 1482071 := bstep (se 1 (by rfl) ⟨1111553, by rfl⟩ : syracuseStep 1482071 = 2223107) B2223107
theorem B1482137 : Blo 984595 1482137 := bstep (se 2 (by rfl) ⟨555801, by rfl⟩ : syracuseStep 1482137 = 1111603) B1111603
theorem B1875467 : Blo 984595 1875467 := bstep (se 1 (by rfl) ⟨1406600, by rfl⟩ : syracuseStep 1875467 = 2813201) B2813201
theorem B1482251 : Blo 984595 1482251 := bstep (se 1 (by rfl) ⟨1111688, by rfl⟩ : syracuseStep 1482251 = 2223377) B2223377
theorem B1482263 : Blo 984595 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B1482329 : Blo 984595 1482329 := bstep (se 2 (by rfl) ⟨555873, by rfl⟩ : syracuseStep 1482329 = 1111747) B1111747
theorem B1875649 : Blo 984595 1875649 := bstep (se 2 (by rfl) ⟨703368, by rfl⟩ : syracuseStep 1875649 = 1406737) B1406737
theorem B1482443 : Blo 984595 1482443 := bstep (se 1 (by rfl) ⟨1111832, by rfl⟩ : syracuseStep 1482443 = 2223665) B2223665
theorem B1482455 : Blo 984595 1482455 := bstep (se 1 (by rfl) ⟨1111841, by rfl⟩ : syracuseStep 1482455 = 2223683) B2223683
theorem B21307121 : Blo 984595 21307121 := bstep (se 2 (by rfl) ⟨7990170, by rfl⟩ : syracuseStep 21307121 = 15980341) B15980341
theorem B1482521 : Blo 984595 1482521 := bstep (se 2 (by rfl) ⟨555945, by rfl⟩ : syracuseStep 1482521 = 1111891) B1111891
theorem B2105227 : Blo 984595 2105227 := bstep (se 1 (by rfl) ⟨1578920, by rfl⟩ : syracuseStep 2105227 = 3157841) B3157841
theorem B1482635 : Blo 984595 1482635 := bstep (se 1 (by rfl) ⟨1111976, by rfl⟩ : syracuseStep 1482635 = 2223953) B2223953
theorem B1482647 : Blo 984595 1482647 := bstep (se 1 (by rfl) ⟨1111985, by rfl⟩ : syracuseStep 1482647 = 2223971) B2223971
theorem B15998897 : Blo 984595 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B1482713 : Blo 984595 1482713 := bstep (se 2 (by rfl) ⟨556017, by rfl⟩ : syracuseStep 1482713 = 1112035) B1112035
theorem B4005953 : Blo 984595 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B1482827 : Blo 984595 1482827 := bstep (se 1 (by rfl) ⟨1112120, by rfl⟩ : syracuseStep 1482827 = 2224241) B2224241
theorem B1482839 : Blo 984595 1482839 := bstep (se 1 (by rfl) ⟨1112129, by rfl⟩ : syracuseStep 1482839 = 2224259) B2224259
theorem B1876097 : Blo 984595 1876097 := bstep (se 2 (by rfl) ⟨703536, by rfl⟩ : syracuseStep 1876097 = 1407073) B1407073
theorem B2105689 : Blo 984595 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B1876439 : Blo 984595 1876439 := bstep (se 1 (by rfl) ⟨1407329, by rfl⟩ : syracuseStep 1876439 = 2814659) B2814659
theorem B6070745 : Blo 984595 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B2499275 : Blo 984595 2499275 := bstep (se 1 (by rfl) ⟨1874456, by rfl⟩ : syracuseStep 2499275 = 3748913) B3748913
theorem B7480025 : Blo 984595 7480025 := bstep (se 2 (by rfl) ⟨2805009, by rfl⟩ : syracuseStep 7480025 = 5610019) B5610019
theorem B4989761 : Blo 984595 4989761 := bstep (se 2 (by rfl) ⟨1871160, by rfl⟩ : syracuseStep 4989761 = 3742321) B3742321
theorem B1123159 : Blo 984595 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B1778903 : Blo 984595 1778903 := bstep (se 1 (by rfl) ⟨1334177, by rfl⟩ : syracuseStep 1778903 = 2668355) B2668355
theorem B4498777 : Blo 984595 4498777 := bstep (se 2 (by rfl) ⟨1687041, by rfl⟩ : syracuseStep 4498777 = 3374083) B3374083
theorem B17114485 : Blo 984595 17114485 := bstep (se 5 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 17114485 = 1604483) B1604483
theorem B2500247 : Blo 984595 2500247 := bstep (se 1 (by rfl) ⟨1875185, by rfl⟩ : syracuseStep 2500247 = 3750371) B3750371
theorem B2107073 : Blo 984595 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B6006545 : Blo 984595 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B3745709 : Blo 984595 3745709 := bstep (se 3 (by rfl) ⟨702320, by rfl⟩ : syracuseStep 3745709 = 1404641) B1404641
theorem B1779659 : Blo 984595 1779659 := bstep (se 1 (by rfl) ⟨1334744, by rfl⟩ : syracuseStep 1779659 = 2669489) B2669489
theorem B2369611 : Blo 984595 2369611 := bstep (se 1 (by rfl) ⟨1777208, by rfl⟩ : syracuseStep 2369611 = 3554417) B3554417
theorem B4499549 : Blo 984595 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B2369843 : Blo 984595 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B2500915 : Blo 984595 2500915 := bstep (se 1 (by rfl) ⟨1875686, by rfl⟩ : syracuseStep 2500915 = 3751373) B3751373
theorem B2501057 : Blo 984595 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B5614211 : Blo 984595 5614211 := bstep (se 1 (by rfl) ⟨4210658, by rfl⟩ : syracuseStep 5614211 = 8421317) B8421317
theorem B3746483 : Blo 984595 3746483 := bstep (se 1 (by rfl) ⟨2809862, by rfl⟩ : syracuseStep 3746483 = 5619725) B5619725
theorem B4991705 : Blo 984595 4991705 := bstep (se 2 (by rfl) ⟨1871889, by rfl⟩ : syracuseStep 4991705 = 3743779) B3743779
theorem B5614667 : Blo 984595 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B2370649 : Blo 984595 2370649 := bstep (se 2 (by rfl) ⟨888993, by rfl⟩ : syracuseStep 2370649 = 1777987) B1777987
theorem B3288385 : Blo 984595 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B2108747 : Blo 984595 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B2371033 : Blo 984595 2371033 := bstep (se 2 (by rfl) ⟨889137, by rfl⟩ : syracuseStep 2371033 = 1778275) B1778275
theorem B1781209 : Blo 984595 1781209 := bstep (se 2 (by rfl) ⟨667953, by rfl⟩ : syracuseStep 1781209 = 1335907) B1335907
theorem B2403929 : Blo 984595 2403929 := bstep (se 2 (by rfl) ⟨901473, by rfl⟩ : syracuseStep 2403929 = 1802947) B1802947
theorem B2502323 : Blo 984595 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B2371265 : Blo 984595 2371265 := bstep (se 2 (by rfl) ⟨889224, by rfl⟩ : syracuseStep 2371265 = 1778449) B1778449
theorem B2666201 : Blo 984595 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B2666333 : Blo 984595 2666333 := bstep (se 3 (by rfl) ⟨499937, by rfl⟩ : syracuseStep 2666333 = 999875) B999875
theorem B34156505 : Blo 984595 34156505 := bstep (se 2 (by rfl) ⟨12808689, by rfl⟩ : syracuseStep 34156505 = 25617379) B25617379
theorem B7483427 : Blo 984595 7483427 := bstep (se 1 (by rfl) ⟨5612570, by rfl⟩ : syracuseStep 7483427 = 11225141) B11225141
theorem B3747971 : Blo 984595 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B16888013 : Blo 984595 16888013 := bstep (se 3 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 16888013 = 6333005) B6333005
theorem B2109721 : Blo 984595 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B4993325 : Blo 984595 4993325 := bstep (se 3 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 4993325 = 1872497) B1872497
theorem B2109977 : Blo 984595 2109977 := bstep (se 2 (by rfl) ⟨791241, by rfl⟩ : syracuseStep 2109977 = 1582483) B1582483
theorem B3551809 : Blo 984595 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B3748427 : Blo 984595 3748427 := bstep (se 1 (by rfl) ⟨2811320, by rfl⟩ : syracuseStep 3748427 = 5622641) B5622641
theorem B3748625 : Blo 984595 3748625 := bstep (se 2 (by rfl) ⟨1405734, by rfl⟩ : syracuseStep 3748625 = 2811469) B2811469
theorem B2372417 : Blo 984595 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B2110387 : Blo 984595 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B35042485 : Blo 984595 35042485 := bstep (se 5 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 35042485 = 3285233) B3285233
theorem B3323159 : Blo 984595 3323159 := bstep (se 1 (by rfl) ⟨2492369, by rfl⟩ : syracuseStep 3323159 = 4984739) B4984739
theorem B3421505 : Blo 984595 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B38417813 : Blo 984595 38417813 := bstep (se 6 (by rfl) ⟨900417, by rfl⟩ : syracuseStep 38417813 = 1800835) B1800835
theorem B8435123 : Blo 984595 8435123 := bstep (se 1 (by rfl) ⟨6326342, by rfl⟩ : syracuseStep 8435123 = 12652685) B12652685
theorem B3749399 : Blo 984595 3749399 := bstep (se 1 (by rfl) ⟨2812049, by rfl⟩ : syracuseStep 3749399 = 5624099) B5624099
theorem B2111105 : Blo 984595 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B3749597 : Blo 984595 3749597 := bstep (se 3 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 3749597 = 1406099) B1406099
theorem B8435501 : Blo 984595 8435501 := bstep (se 3 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 8435501 = 3163313) B3163313
theorem B3323699 : Blo 984595 3323699 := bstep (se 1 (by rfl) ⟨2492774, by rfl⟩ : syracuseStep 3323699 = 4985549) B4985549
theorem B3323969 : Blo 984595 3323969 := bstep (se 2 (by rfl) ⟨1246488, by rfl⟩ : syracuseStep 3323969 = 2492977) B2492977
theorem B4209155 : Blo 984595 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B3324509 : Blo 984595 3324509 := bstep (se 3 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 3324509 = 1246691) B1246691
theorem B4734301 : Blo 984595 4734301 := bstep (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) B1775363
theorem B3554705 : Blo 984595 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B4505053 : Blo 984595 4505053 := bstep (se 3 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 4505053 = 1689395) B1689395
theorem B5619293 : Blo 984595 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B3751555 : Blo 984595 3751555 := bstep (se 1 (by rfl) ⟨2813666, by rfl⟩ : syracuseStep 3751555 = 5627333) B5627333
theorem B2997911 : Blo 984595 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B3325643 : Blo 984595 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B3555037 : Blo 984595 3555037 := bstep (se 3 (by rfl) ⟨666569, by rfl⟩ : syracuseStep 3555037 = 1333139) B1333139
theorem B1425163 : Blo 984595 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B3161879 : Blo 984595 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B999307 : Blo 984595 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B3751859 : Blo 984595 3751859 := bstep (se 1 (by rfl) ⟨2813894, by rfl⟩ : syracuseStep 3751859 = 5627789) B5627789
theorem B17121203 : Blo 984595 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B3325913 : Blo 984595 3325913 := bstep (se 2 (by rfl) ⟨1247217, by rfl⟩ : syracuseStep 3325913 = 2494435) B2494435
theorem B2998237 : Blo 984595 2998237 := bstep (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) B1124339
theorem B4997213 : Blo 984595 4997213 := bstep (se 3 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 4997213 = 1873955) B1873955
theorem B999595 : Blo 984595 999595 := bstep (se 1 (by rfl) ⟨749696, by rfl⟩ : syracuseStep 999595 = 1499393) B1499393
theorem B4210967 : Blo 984595 4210967 := bstep (se 1 (by rfl) ⟨3158225, by rfl⟩ : syracuseStep 4210967 = 6316451) B6316451
theorem B5620043 : Blo 984595 5620043 := bstep (se 1 (by rfl) ⟨4215032, by rfl⟩ : syracuseStep 5620043 = 8430065) B8430065
theorem B2703709 : Blo 984595 2703709 := bstep (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) B1013891
theorem B3555857 : Blo 984595 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B3752513 : Blo 984595 3752513 := bstep (se 2 (by rfl) ⟨1407192, by rfl⟩ : syracuseStep 3752513 = 2814385) B2814385
theorem B11223683 : Blo 984595 11223683 := bstep (se 1 (by rfl) ⟨8417762, by rfl⟩ : syracuseStep 11223683 = 16835525) B16835525
theorem B3326615 : Blo 984595 3326615 := bstep (se 1 (by rfl) ⟨2494961, by rfl⟩ : syracuseStep 3326615 = 4989923) B4989923
theorem B1000459 : Blo 984595 1000459 := bstep (se 1 (by rfl) ⟨750344, by rfl⟩ : syracuseStep 1000459 = 1500689) B1500689
theorem B4277393 : Blo 984595 4277393 := bstep (se 2 (by rfl) ⟨1604022, by rfl⟩ : syracuseStep 4277393 = 3208045) B3208045
theorem B3327155 : Blo 984595 3327155 := bstep (se 1 (by rfl) ⟨2495366, by rfl⟩ : syracuseStep 3327155 = 4990733) B4990733
theorem B7488773 : Blo 984595 7488773 := bstep (se 4 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 7488773 = 1404145) B1404145
theorem B1852723 : Blo 984595 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B3327425 : Blo 984595 3327425 := bstep (se 2 (by rfl) ⟨1247784, by rfl⟩ : syracuseStep 3327425 = 2495569) B2495569
theorem B2246105 : Blo 984595 2246105 := bstep (se 2 (by rfl) ⟨842289, by rfl⟩ : syracuseStep 2246105 = 1684579) B1684579
theorem B4212299 : Blo 984595 4212299 := bstep (se 1 (by rfl) ⟨3159224, by rfl⟩ : syracuseStep 4212299 = 6318449) B6318449
theorem B1689355 : Blo 984595 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B5621683 : Blo 984595 5621683 := bstep (se 1 (by rfl) ⟨4216262, by rfl⟩ : syracuseStep 5621683 = 8432525) B8432525
theorem B6932441 : Blo 984595 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B3327965 : Blo 984595 3327965 := bstep (se 3 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 3327965 = 1247987) B1247987
theorem B4507613 : Blo 984595 4507613 := bstep (se 3 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 4507613 = 1690355) B1690355
theorem B4212881 : Blo 984595 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B4999319 : Blo 984595 4999319 := bstep (se 1 (by rfl) ⟨3749489, by rfl⟩ : syracuseStep 4999319 = 7498979) B7498979
theorem B3164339 : Blo 984595 3164339 := bstep (se 1 (by rfl) ⟨2373254, by rfl⟩ : syracuseStep 3164339 = 4746509) B4746509
theorem B1001975 : Blo 984595 1001975 := bstep (se 1 (by rfl) ⟨751481, by rfl⟩ : syracuseStep 1001975 = 1502963) B1502963
theorem B17975843 : Blo 984595 17975843 := bstep (se 1 (by rfl) ⟨13481882, by rfl⟩ : syracuseStep 17975843 = 26963765) B26963765
theorem B5557123 : Blo 984595 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B3329099 : Blo 984595 3329099 := bstep (se 1 (by rfl) ⟨2496824, by rfl⟩ : syracuseStep 3329099 = 4993649) B4993649
theorem B4213939 : Blo 984595 4213939 := bstep (se 1 (by rfl) ⟨3160454, by rfl⟩ : syracuseStep 4213939 = 6320909) B6320909
theorem B3329369 : Blo 984595 3329369 := bstep (se 2 (by rfl) ⟨1248513, by rfl⟩ : syracuseStep 3329369 = 2497027) B2497027
theorem B5623141 : Blo 984595 5623141 := bstep (se 4 (by rfl) ⟨527169, by rfl⟩ : syracuseStep 5623141 = 1054339) B1054339
theorem B5066135 : Blo 984595 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B2215385 : Blo 984595 2215385 := bstep (se 2 (by rfl) ⟨830769, by rfl⟩ : syracuseStep 2215385 = 1661539) B1661539
theorem B2215475 : Blo 984595 2215475 := bstep (se 1 (by rfl) ⟨1661606, by rfl⟩ : syracuseStep 2215475 = 3323213) B3323213
theorem B2215511 : Blo 984595 2215511 := bstep (se 1 (by rfl) ⟨1661633, by rfl⟩ : syracuseStep 2215511 = 3323267) B3323267
theorem B7491203 : Blo 984595 7491203 := bstep (se 1 (by rfl) ⟨5618402, by rfl⟩ : syracuseStep 7491203 = 11236805) B11236805
theorem B2215691 : Blo 984595 2215691 := bstep (se 1 (by rfl) ⟨1661768, by rfl⟩ : syracuseStep 2215691 = 3323537) B3323537
theorem B2215745 : Blo 984595 2215745 := bstep (se 2 (by rfl) ⟨830904, by rfl⟩ : syracuseStep 2215745 = 1661809) B1661809
theorem B14241653 : Blo 984595 14241653 := bstep (se 5 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 14241653 = 1335155) B1335155
theorem B3330071 : Blo 984595 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B2215961 : Blo 984595 2215961 := bstep (se 2 (by rfl) ⟨830985, by rfl⟩ : syracuseStep 2215961 = 1661971) B1661971
theorem B7589963 : Blo 984595 7589963 := bstep (se 1 (by rfl) ⟨5692472, by rfl⟩ : syracuseStep 7589963 = 11384945) B11384945
theorem B2805853 : Blo 984595 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B2216051 : Blo 984595 2216051 := bstep (se 1 (by rfl) ⟨1662038, by rfl⟩ : syracuseStep 2216051 = 3324077) B3324077
theorem B2216087 : Blo 984595 2216087 := bstep (se 1 (by rfl) ⟨1662065, by rfl⟩ : syracuseStep 2216087 = 3324131) B3324131
theorem B2805911 : Blo 984595 2805911 := bstep (se 1 (by rfl) ⟨2104433, by rfl⟩ : syracuseStep 2805911 = 4208867) B4208867
theorem B2216267 : Blo 984595 2216267 := bstep (se 1 (by rfl) ⟨1662200, by rfl⟩ : syracuseStep 2216267 = 3324401) B3324401
theorem B2216321 : Blo 984595 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B4215341 : Blo 984595 4215341 := bstep (se 3 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 4215341 = 1580753) B1580753
theorem B3330611 : Blo 984595 3330611 := bstep (se 1 (by rfl) ⟨2497958, by rfl⟩ : syracuseStep 3330611 = 4995917) B4995917
theorem B2216537 : Blo 984595 2216537 := bstep (se 2 (by rfl) ⟨831201, by rfl⟩ : syracuseStep 2216537 = 1662403) B1662403
theorem B1921687 : Blo 984595 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B2216627 : Blo 984595 2216627 := bstep (se 1 (by rfl) ⟨1662470, by rfl⟩ : syracuseStep 2216627 = 3324941) B3324941
theorem B2708147 : Blo 984595 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B3166913 : Blo 984595 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B2216663 : Blo 984595 2216663 := bstep (se 1 (by rfl) ⟨1662497, by rfl⟩ : syracuseStep 2216663 = 3324995) B3324995
theorem B3330881 : Blo 984595 3330881 := bstep (se 2 (by rfl) ⟨1249080, by rfl⟩ : syracuseStep 3330881 = 2498161) B2498161
theorem B2216843 : Blo 984595 2216843 := bstep (se 1 (by rfl) ⟨1662632, by rfl⟩ : syracuseStep 2216843 = 3325265) B3325265
theorem B3789719 : Blo 984595 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B2216897 : Blo 984595 2216897 := bstep (se 2 (by rfl) ⟨831336, by rfl⟩ : syracuseStep 2216897 = 1662673) B1662673
theorem B2217113 : Blo 984595 2217113 := bstep (se 2 (by rfl) ⟨831417, by rfl⟩ : syracuseStep 2217113 = 1662835) B1662835
theorem B2217203 : Blo 984595 2217203 := bstep (se 1 (by rfl) ⟨1662902, by rfl⟩ : syracuseStep 2217203 = 3325805) B3325805
theorem B2217239 : Blo 984595 2217239 := bstep (se 1 (by rfl) ⟨1662929, by rfl⟩ : syracuseStep 2217239 = 3325859) B3325859
theorem B3003713 : Blo 984595 3003713 := bstep (se 2 (by rfl) ⟨1126392, by rfl⟩ : syracuseStep 3003713 = 2252785) B2252785
theorem B2807129 : Blo 984595 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B3331421 : Blo 984595 3331421 := bstep (se 3 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 3331421 = 1249283) B1249283
theorem B2217419 : Blo 984595 2217419 := bstep (se 1 (by rfl) ⟨1663064, by rfl⟩ : syracuseStep 2217419 = 3326129) B3326129
theorem B2807243 : Blo 984595 2807243 := bstep (se 1 (by rfl) ⟨2105432, by rfl⟩ : syracuseStep 2807243 = 4210865) B4210865
theorem B2217473 : Blo 984595 2217473 := bstep (se 2 (by rfl) ⟨831552, by rfl⟩ : syracuseStep 2217473 = 1663105) B1663105
theorem B1267211 : Blo 984595 1267211 := bstep (se 1 (by rfl) ⟨950408, by rfl⟩ : syracuseStep 1267211 = 1900817) B1900817
theorem B5002883 : Blo 984595 5002883 := bstep (se 1 (by rfl) ⟨3752162, by rfl⟩ : syracuseStep 5002883 = 7504325) B7504325
theorem B2217689 : Blo 984595 2217689 := bstep (se 2 (by rfl) ⟨831633, by rfl⟩ : syracuseStep 2217689 = 1663267) B1663267
theorem B2217779 : Blo 984595 2217779 := bstep (se 1 (by rfl) ⟨1663334, by rfl⟩ : syracuseStep 2217779 = 3326669) B3326669
theorem B3004235 : Blo 984595 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B2217815 : Blo 984595 2217815 := bstep (se 1 (by rfl) ⟨1663361, by rfl⟩ : syracuseStep 2217815 = 3326723) B3326723
theorem B1333079 : Blo 984595 1333079 := bstep (se 1 (by rfl) ⟨999809, by rfl⟩ : syracuseStep 1333079 = 1999619) B1999619
theorem B3790795 : Blo 984595 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B2217995 : Blo 984595 2217995 := bstep (se 1 (by rfl) ⟨1663496, by rfl⟩ : syracuseStep 2217995 = 3326993) B3326993
theorem B2250775 : Blo 984595 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B2218049 : Blo 984595 2218049 := bstep (se 2 (by rfl) ⟨831768, by rfl⟩ : syracuseStep 2218049 = 1663537) B1663537
theorem B30365765 : Blo 984595 30365765 := bstep (se 4 (by rfl) ⟨2846790, by rfl⟩ : syracuseStep 30365765 = 5693581) B5693581
theorem B2250841 : Blo 984595 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B7100621 : Blo 984595 7100621 := bstep (se 3 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 7100621 = 2662733) B2662733
theorem B2218265 : Blo 984595 2218265 := bstep (se 2 (by rfl) ⟨831849, by rfl⟩ : syracuseStep 2218265 = 1663699) B1663699
theorem B2218355 : Blo 984595 2218355 := bstep (se 1 (by rfl) ⟨1663766, by rfl⟩ : syracuseStep 2218355 = 3327533) B3327533
theorem B2218391 : Blo 984595 2218391 := bstep (se 1 (by rfl) ⟨1663793, by rfl⟩ : syracuseStep 2218391 = 3327587) B3327587
theorem B3332555 : Blo 984595 3332555 := bstep (se 1 (by rfl) ⟨2499416, by rfl⟩ : syracuseStep 3332555 = 4998833) B4998833
theorem B3562001 : Blo 984595 3562001 := bstep (se 2 (by rfl) ⟨1335750, by rfl⟩ : syracuseStep 3562001 = 2671501) B2671501
theorem B2808371 : Blo 984595 2808371 := bstep (se 1 (by rfl) ⟨2106278, by rfl⟩ : syracuseStep 2808371 = 4212557) B4212557
theorem B2218571 : Blo 984595 2218571 := bstep (se 1 (by rfl) ⟨1663928, by rfl⟩ : syracuseStep 2218571 = 3327857) B3327857
theorem B2218625 : Blo 984595 2218625 := bstep (se 2 (by rfl) ⟨831984, by rfl⟩ : syracuseStep 2218625 = 1663969) B1663969
theorem B1661593 : Blo 984595 1661593 := bstep (se 2 (by rfl) ⟨623097, by rfl⟩ : syracuseStep 1661593 = 1246195) B1246195
theorem B7101107 : Blo 984595 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B3332825 : Blo 984595 3332825 := bstep (se 2 (by rfl) ⟨1249809, by rfl⟩ : syracuseStep 3332825 = 2499619) B2499619
theorem B2218841 : Blo 984595 2218841 := bstep (se 2 (by rfl) ⟨832065, by rfl⟩ : syracuseStep 2218841 = 1664131) B1664131
theorem B2218931 : Blo 984595 2218931 := bstep (se 1 (by rfl) ⟨1664198, by rfl⟩ : syracuseStep 2218931 = 3328397) B3328397
theorem B2808769 : Blo 984595 2808769 := bstep (se 2 (by rfl) ⟨1053288, by rfl⟩ : syracuseStep 2808769 = 2106577) B2106577
theorem B7494605 : Blo 984595 7494605 := bstep (se 3 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 7494605 = 2810477) B2810477
theorem B2218967 : Blo 984595 2218967 := bstep (se 1 (by rfl) ⟨1664225, by rfl⟩ : syracuseStep 2218967 = 3328451) B3328451
theorem B2219147 : Blo 984595 2219147 := bstep (se 1 (by rfl) ⟨1664360, by rfl⟩ : syracuseStep 2219147 = 3328721) B3328721
theorem B2219201 : Blo 984595 2219201 := bstep (se 2 (by rfl) ⟨832200, by rfl⟩ : syracuseStep 2219201 = 1664401) B1664401
theorem B3005633 : Blo 984595 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B1662167 : Blo 984595 1662167 := bstep (se 1 (by rfl) ⟨1246625, by rfl⟩ : syracuseStep 1662167 = 2493251) B2493251
theorem B1334551 : Blo 984595 1334551 := bstep (se 1 (by rfl) ⟨1000913, by rfl⟩ : syracuseStep 1334551 = 2001827) B2001827
theorem B13491521 : Blo 984595 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B1662295 : Blo 984595 1662295 := bstep (se 1 (by rfl) ⟨1246721, by rfl⟩ : syracuseStep 1662295 = 2493443) B2493443
theorem B3333527 : Blo 984595 3333527 := bstep (se 1 (by rfl) ⟨2500145, by rfl⟩ : syracuseStep 3333527 = 5000291) B5000291
theorem B2219417 : Blo 984595 2219417 := bstep (se 2 (by rfl) ⟨832281, by rfl⟩ : syracuseStep 2219417 = 1664563) B1664563
theorem B7495091 : Blo 984595 7495091 := bstep (se 1 (by rfl) ⟨5621318, by rfl⟩ : syracuseStep 7495091 = 11242637) B11242637
theorem B2219507 : Blo 984595 2219507 := bstep (se 1 (by rfl) ⟨1664630, by rfl⟩ : syracuseStep 2219507 = 3329261) B3329261
theorem B2219543 : Blo 984595 2219543 := bstep (se 1 (by rfl) ⟨1664657, by rfl⟩ : syracuseStep 2219543 = 3329315) B3329315
theorem B4808323 : Blo 984595 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B2219723 : Blo 984595 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B2219777 : Blo 984595 2219777 := bstep (se 2 (by rfl) ⟨832416, by rfl⟩ : syracuseStep 2219777 = 1664833) B1664833
theorem B3334067 : Blo 984595 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B1662923 : Blo 984595 1662923 := bstep (se 1 (by rfl) ⟨1247192, by rfl⟩ : syracuseStep 1662923 = 2494385) B2494385
theorem B2219993 : Blo 984595 2219993 := bstep (se 2 (by rfl) ⟨832497, by rfl⟩ : syracuseStep 2219993 = 1664995) B1664995
theorem B2220083 : Blo 984595 2220083 := bstep (se 1 (by rfl) ⟨1665062, by rfl⟩ : syracuseStep 2220083 = 3330125) B3330125
theorem B1663051 : Blo 984595 1663051 := bstep (se 1 (by rfl) ⟨1247288, by rfl⟩ : syracuseStep 1663051 = 2494577) B2494577
theorem B2220119 : Blo 984595 2220119 := bstep (se 1 (by rfl) ⟨1665089, by rfl⟩ : syracuseStep 2220119 = 3330179) B3330179
theorem B3334337 : Blo 984595 3334337 := bstep (se 2 (by rfl) ⟨1250376, by rfl⟩ : syracuseStep 3334337 = 2500753) B2500753
theorem B10117325 : Blo 984595 10117325 := bstep (se 3 (by rfl) ⟨1896998, by rfl⟩ : syracuseStep 10117325 = 3793997) B3793997
theorem B1663193 : Blo 984595 1663193 := bstep (se 2 (by rfl) ⟨623697, by rfl⟩ : syracuseStep 1663193 = 1247395) B1247395
theorem B2220299 : Blo 984595 2220299 := bstep (se 1 (by rfl) ⟨1665224, by rfl⟩ : syracuseStep 2220299 = 3330449) B3330449
theorem B3793169 : Blo 984595 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B2220353 : Blo 984595 2220353 := bstep (se 2 (by rfl) ⟨832632, by rfl⟩ : syracuseStep 2220353 = 1665265) B1665265
theorem B1663321 : Blo 984595 1663321 := bstep (se 2 (by rfl) ⟨623745, by rfl⟩ : syracuseStep 1663321 = 1247491) B1247491
theorem B2220569 : Blo 984595 2220569 := bstep (se 2 (by rfl) ⟨832713, by rfl⟩ : syracuseStep 2220569 = 1665427) B1665427
theorem B7103011 : Blo 984595 7103011 := bstep (se 1 (by rfl) ⟨5327258, by rfl⟩ : syracuseStep 7103011 = 10654517) B10654517
theorem B2220659 : Blo 984595 2220659 := bstep (se 1 (by rfl) ⟨1665494, by rfl⟩ : syracuseStep 2220659 = 3330989) B3330989
theorem B2220695 : Blo 984595 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B4219543 : Blo 984595 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B4219613 : Blo 984595 4219613 := bstep (se 3 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 4219613 = 1582355) B1582355
theorem B3334877 : Blo 984595 3334877 := bstep (se 3 (by rfl) ⟨625289, by rfl⟩ : syracuseStep 3334877 = 1250579) B1250579
theorem B4743953 : Blo 984595 4743953 := bstep (se 2 (by rfl) ⟨1778982, by rfl⟩ : syracuseStep 4743953 = 3557965) B3557965
theorem B10969901 : Blo 984595 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B2220875 : Blo 984595 2220875 := bstep (se 1 (by rfl) ⟨1665656, by rfl⟩ : syracuseStep 2220875 = 3331313) B3331313
theorem B7496549 : Blo 984595 7496549 := bstep (se 4 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 7496549 = 1405603) B1405603
theorem B2220929 : Blo 984595 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B1663895 : Blo 984595 1663895 := bstep (se 1 (by rfl) ⟨1247921, by rfl⟩ : syracuseStep 1663895 = 2495843) B2495843
theorem B1664023 : Blo 984595 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B5628973 : Blo 984595 5628973 := bstep (se 3 (by rfl) ⟨1055432, by rfl⟩ : syracuseStep 5628973 = 2110865) B2110865
theorem B2221145 : Blo 984595 2221145 := bstep (se 2 (by rfl) ⟨832929, by rfl⟩ : syracuseStep 2221145 = 1665859) B1665859
theorem B2221235 : Blo 984595 2221235 := bstep (se 1 (by rfl) ⟨1665926, by rfl⟩ : syracuseStep 2221235 = 3331853) B3331853
theorem B2221271 : Blo 984595 2221271 := bstep (se 1 (by rfl) ⟨1665953, by rfl⟩ : syracuseStep 2221271 = 3331907) B3331907
theorem B7497035 : Blo 984595 7497035 := bstep (se 1 (by rfl) ⟨5622776, by rfl⟩ : syracuseStep 7497035 = 11245553) B11245553
theorem B2221451 : Blo 984595 2221451 := bstep (se 1 (by rfl) ⟨1666088, by rfl⟩ : syracuseStep 2221451 = 3332177) B3332177
theorem B2811287 : Blo 984595 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B2221505 : Blo 984595 2221505 := bstep (se 2 (by rfl) ⟨833064, by rfl⟩ : syracuseStep 2221505 = 1666129) B1666129
theorem B4220363 : Blo 984595 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B1402391 : Blo 984595 1402391 := bstep (se 1 (by rfl) ⟨1051793, by rfl⟩ : syracuseStep 1402391 = 2103587) B2103587
theorem B1664651 : Blo 984595 1664651 := bstep (se 1 (by rfl) ⟨1248488, by rfl⟩ : syracuseStep 1664651 = 2496977) B2496977
theorem B2221721 : Blo 984595 2221721 := bstep (se 2 (by rfl) ⟨833145, by rfl⟩ : syracuseStep 2221721 = 1666291) B1666291
theorem B2221811 : Blo 984595 2221811 := bstep (se 1 (by rfl) ⟨1666358, by rfl⟩ : syracuseStep 2221811 = 3332717) B3332717
theorem B1664779 : Blo 984595 1664779 := bstep (se 1 (by rfl) ⟨1248584, by rfl⟩ : syracuseStep 1664779 = 2497169) B2497169
theorem B2221847 : Blo 984595 2221847 := bstep (se 1 (by rfl) ⟨1666385, by rfl⟩ : syracuseStep 2221847 = 3332771) B3332771
theorem B1107787 : Blo 984595 1107787 := bstep (se 1 (by rfl) ⟨830840, by rfl⟩ : syracuseStep 1107787 = 1661681) B1661681
theorem B1402699 : Blo 984595 1402699 := bstep (se 1 (by rfl) ⟨1052024, by rfl⟩ : syracuseStep 1402699 = 2104049) B2104049
theorem B3336011 : Blo 984595 3336011 := bstep (se 1 (by rfl) ⟨2502008, by rfl⟩ : syracuseStep 3336011 = 5004017) B5004017
theorem B1664921 : Blo 984595 1664921 := bstep (se 2 (by rfl) ⟨624345, by rfl⟩ : syracuseStep 1664921 = 1248691) B1248691
theorem B12642227 : Blo 984595 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B1107895 : Blo 984595 1107895 := bstep (se 1 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 1107895 = 1661843) B1661843
theorem B2222027 : Blo 984595 2222027 := bstep (se 1 (by rfl) ⟨1666520, by rfl⟩ : syracuseStep 2222027 = 3333041) B3333041
theorem B2222081 : Blo 984595 2222081 := bstep (se 2 (by rfl) ⟨833280, by rfl⟩ : syracuseStep 2222081 = 1666561) B1666561
theorem B1665049 : Blo 984595 1665049 := bstep (se 2 (by rfl) ⟨624393, by rfl⟩ : syracuseStep 1665049 = 1248787) B1248787
theorem B5335085 : Blo 984595 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B3336281 : Blo 984595 3336281 := bstep (se 2 (by rfl) ⟨1251105, by rfl⟩ : syracuseStep 3336281 = 2502211) B2502211
theorem B1108075 : Blo 984595 1108075 := bstep (se 1 (by rfl) ⟨831056, by rfl⟩ : syracuseStep 1108075 = 1662113) B1662113
theorem B1108183 : Blo 984595 1108183 := bstep (se 1 (by rfl) ⟨831137, by rfl⟩ : syracuseStep 1108183 = 1662275) B1662275
theorem B2222297 : Blo 984595 2222297 := bstep (se 2 (by rfl) ⟨833361, by rfl⟩ : syracuseStep 2222297 = 1666723) B1666723
theorem B7989521 : Blo 984595 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B16017709 : Blo 984595 16017709 := bstep (se 3 (by rfl) ⟨3003320, by rfl⟩ : syracuseStep 16017709 = 6006641) B6006641
theorem B2222387 : Blo 984595 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B2222423 : Blo 984595 2222423 := bstep (se 1 (by rfl) ⟨1666817, by rfl⟩ : syracuseStep 2222423 = 3333635) B3333635
theorem B4745603 : Blo 984595 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B1108363 : Blo 984595 1108363 := bstep (se 1 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 1108363 = 1662545) B1662545
theorem B1108471 : Blo 984595 1108471 := bstep (se 1 (by rfl) ⟨831353, by rfl⟩ : syracuseStep 1108471 = 1662707) B1662707
theorem B2222603 : Blo 984595 2222603 := bstep (se 1 (by rfl) ⟨1666952, by rfl⟩ : syracuseStep 2222603 = 3333905) B3333905
theorem B2222657 : Blo 984595 2222657 := bstep (se 2 (by rfl) ⟨833496, by rfl⟩ : syracuseStep 2222657 = 1666993) B1666993
theorem B1665623 : Blo 984595 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B1108651 : Blo 984595 1108651 := bstep (se 1 (by rfl) ⟨831488, by rfl⟩ : syracuseStep 1108651 = 1662977) B1662977
theorem B2812619 : Blo 984595 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B1665751 : Blo 984595 1665751 := bstep (se 1 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 1665751 = 2498627) B2498627
theorem B1108759 : Blo 984595 1108759 := bstep (se 1 (by rfl) ⟨831569, by rfl⟩ : syracuseStep 1108759 = 1663139) B1663139
theorem B2222873 : Blo 984595 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B1403735 : Blo 984595 1403735 := bstep (se 1 (by rfl) ⟨1052801, by rfl⟩ : syracuseStep 1403735 = 2105603) B2105603
theorem B1502039 : Blo 984595 1502039 := bstep (se 1 (by rfl) ⟨1126529, by rfl⟩ : syracuseStep 1502039 = 2253059) B2253059
theorem B2222963 : Blo 984595 2222963 := bstep (se 1 (by rfl) ⟨1667222, by rfl⟩ : syracuseStep 2222963 = 3334445) B3334445
theorem B2222999 : Blo 984595 2222999 := bstep (se 1 (by rfl) ⟨1667249, by rfl⟩ : syracuseStep 2222999 = 3334499) B3334499
theorem B1108939 : Blo 984595 1108939 := bstep (se 1 (by rfl) ⟨831704, by rfl⟩ : syracuseStep 1108939 = 1663409) B1663409
theorem B1403929 : Blo 984595 1403929 := bstep (se 2 (by rfl) ⟨526473, by rfl⟩ : syracuseStep 1403929 = 1052947) B1052947
theorem B1109047 : Blo 984595 1109047 := bstep (se 1 (by rfl) ⟨831785, by rfl⟩ : syracuseStep 1109047 = 1663571) B1663571
theorem B2223179 : Blo 984595 2223179 := bstep (se 1 (by rfl) ⟨1667384, by rfl⟩ : syracuseStep 2223179 = 3334769) B3334769
theorem B2223233 : Blo 984595 2223233 := bstep (se 2 (by rfl) ⟨833712, by rfl⟩ : syracuseStep 2223233 = 1667425) B1667425
theorem B1109227 : Blo 984595 1109227 := bstep (se 1 (by rfl) ⟨831920, by rfl⟩ : syracuseStep 1109227 = 1663841) B1663841
theorem B1666379 : Blo 984595 1666379 := bstep (se 1 (by rfl) ⟨1249784, by rfl⟩ : syracuseStep 1666379 = 2499569) B2499569
theorem B1109335 : Blo 984595 1109335 := bstep (se 1 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 1109335 = 1664003) B1664003
theorem B2223449 : Blo 984595 2223449 := bstep (se 2 (by rfl) ⟨833793, by rfl⟩ : syracuseStep 2223449 = 1667587) B1667587
theorem B2223539 : Blo 984595 2223539 := bstep (se 1 (by rfl) ⟨1667654, by rfl⟩ : syracuseStep 2223539 = 3335309) B3335309
theorem B1666507 : Blo 984595 1666507 := bstep (se 1 (by rfl) ⟨1249880, by rfl⟩ : syracuseStep 1666507 = 2499761) B2499761
theorem B2223575 : Blo 984595 2223575 := bstep (se 1 (by rfl) ⟨1667681, by rfl⟩ : syracuseStep 2223575 = 3335363) B3335363
theorem B1109515 : Blo 984595 1109515 := bstep (se 1 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 1109515 = 1664273) B1664273
theorem B31157777 : Blo 984595 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B1666649 : Blo 984595 1666649 := bstep (se 2 (by rfl) ⟨624993, by rfl⟩ : syracuseStep 1666649 = 1249987) B1249987
theorem B1109623 : Blo 984595 1109623 := bstep (se 1 (by rfl) ⟨832217, by rfl⟩ : syracuseStep 1109623 = 1664435) B1664435
theorem B2223755 : Blo 984595 2223755 := bstep (se 1 (by rfl) ⟨1667816, by rfl⟩ : syracuseStep 2223755 = 3335633) B3335633
theorem B2223809 : Blo 984595 2223809 := bstep (se 2 (by rfl) ⟨833928, by rfl⟩ : syracuseStep 2223809 = 1667857) B1667857
theorem B1666777 : Blo 984595 1666777 := bstep (se 2 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 1666777 = 1250083) B1250083
theorem B1109803 : Blo 984595 1109803 := bstep (se 1 (by rfl) ⟨832352, by rfl⟩ : syracuseStep 1109803 = 1664705) B1664705
theorem B1109911 : Blo 984595 1109911 := bstep (se 1 (by rfl) ⟨832433, by rfl⟩ : syracuseStep 1109911 = 1664867) B1664867
theorem B2224025 : Blo 984595 2224025 := bstep (se 2 (by rfl) ⟨834009, by rfl⟩ : syracuseStep 2224025 = 1668019) B1668019
theorem B2224115 : Blo 984595 2224115 := bstep (se 1 (by rfl) ⟨1668086, by rfl⟩ : syracuseStep 2224115 = 3336173) B3336173
theorem B2224151 : Blo 984595 2224151 := bstep (se 1 (by rfl) ⟨1668113, by rfl⟩ : syracuseStep 2224151 = 3336227) B3336227
theorem B1110091 : Blo 984595 1110091 := bstep (se 1 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 1110091 = 1665137) B1665137
theorem B1110199 : Blo 984595 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B2224331 : Blo 984595 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B1667351 : Blo 984595 1667351 := bstep (se 1 (by rfl) ⟨1250513, by rfl⟩ : syracuseStep 1667351 = 2501027) B2501027
theorem B2814259 : Blo 984595 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B5337419 : Blo 984595 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B1110379 : Blo 984595 1110379 := bstep (se 1 (by rfl) ⟨832784, by rfl⟩ : syracuseStep 1110379 = 1665569) B1665569
theorem B2027891 : Blo 984595 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B1667479 : Blo 984595 1667479 := bstep (se 1 (by rfl) ⟨1250609, by rfl⟩ : syracuseStep 1667479 = 2501219) B2501219
theorem B1405387 : Blo 984595 1405387 := bstep (se 1 (by rfl) ⟨1054040, by rfl⟩ : syracuseStep 1405387 = 2108081) B2108081
theorem B1110487 : Blo 984595 1110487 := bstep (se 1 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 1110487 = 1665731) B1665731
theorem B1110667 : Blo 984595 1110667 := bstep (se 1 (by rfl) ⟨833000, by rfl⟩ : syracuseStep 1110667 = 1666001) B1666001
theorem B1110775 : Blo 984595 1110775 := bstep (se 1 (by rfl) ⟨833081, by rfl⟩ : syracuseStep 1110775 = 1666163) B1666163
theorem B24343361 : Blo 984595 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B1110955 : Blo 984595 1110955 := bstep (se 1 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 1110955 = 1666433) B1666433
theorem B1668107 : Blo 984595 1668107 := bstep (se 1 (by rfl) ⟨1251080, by rfl⟩ : syracuseStep 1668107 = 2502161) B2502161
theorem B1111063 : Blo 984595 1111063 := bstep (se 1 (by rfl) ⟨833297, by rfl⟩ : syracuseStep 1111063 = 1666595) B1666595
theorem B1668235 : Blo 984595 1668235 := bstep (se 1 (by rfl) ⟨1251176, by rfl⟩ : syracuseStep 1668235 = 2502353) B2502353
theorem B1111243 : Blo 984595 1111243 := bstep (se 1 (by rfl) ⟨833432, by rfl⟩ : syracuseStep 1111243 = 1666865) B1666865
theorem B35058989 : Blo 984595 35058989 := bstep (se 3 (by rfl) ⟨6573560, by rfl⟩ : syracuseStep 35058989 = 13147121) B13147121
theorem B1111351 : Blo 984595 1111351 := bstep (se 1 (by rfl) ⟨833513, by rfl⟩ : syracuseStep 1111351 = 1667027) B1667027
theorem B8418653 : Blo 984595 8418653 := bstep (se 3 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 8418653 = 3156995) B3156995
theorem B1111531 : Blo 984595 1111531 := bstep (se 1 (by rfl) ⟨833648, by rfl⟩ : syracuseStep 1111531 = 1667297) B1667297
theorem B1111639 : Blo 984595 1111639 := bstep (se 1 (by rfl) ⟨833729, by rfl⟩ : syracuseStep 1111639 = 1667459) B1667459
theorem B89028209 : Blo 984595 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B1111819 : Blo 984595 1111819 := bstep (se 1 (by rfl) ⟨833864, by rfl⟩ : syracuseStep 1111819 = 1667729) B1667729
theorem B1111927 : Blo 984595 1111927 := bstep (se 1 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 1111927 = 1667891) B1667891
theorem B1112107 : Blo 984595 1112107 := bstep (se 1 (by rfl) ⟨834080, by rfl⟩ : syracuseStep 1112107 = 1668161) B1668161
theorem B8419403 : Blo 984595 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B3209291 : Blo 984595 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B10647683 : Blo 984595 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B3996125 : Blo 984595 3996125 := bstep (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) B1498547
theorem B7502381 : Blo 984595 7502381 := bstep (se 3 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 7502381 = 2813393) B2813393
theorem B3996823 : Blo 984595 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B3374401 : Blo 984595 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B1998283 : Blo 984595 1998283 := bstep (se 1 (by rfl) ⟨1498712, by rfl⟩ : syracuseStep 1998283 = 2997425) B2997425
theorem B8421043 : Blo 984595 8421043 := bstep (se 1 (by rfl) ⟨6315782, by rfl⟩ : syracuseStep 8421043 = 12631565) B12631565
theorem B45547541 : Blo 984595 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B9470681 : Blo 984595 9470681 := bstep (se 2 (by rfl) ⟨3551505, by rfl⟩ : syracuseStep 9470681 = 7103011) B7103011
theorem B2851595 : Blo 984595 2851595 := bstep (se 1 (by rfl) ⟨2138696, by rfl⟩ : syracuseStep 2851595 = 4277393) B4277393
theorem B16188653 : Blo 984595 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B4621627 : Blo 984595 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B7505297 : Blo 984595 7505297 := bstep (se 2 (by rfl) ⟨2814486, by rfl⟩ : syracuseStep 7505297 = 5628973) B5628973
theorem B984635 : Blo 984595 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B36537925 : Blo 984595 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B984711 : Blo 984595 984711 := bstep (se 1 (by rfl) ⟨738533, by rfl⟩ : syracuseStep 984711 = 1477067) B1477067
theorem B984719 : Blo 984595 984719 := bstep (se 1 (by rfl) ⟨738539, by rfl⟩ : syracuseStep 984719 = 1477079) B1477079
theorem B984763 : Blo 984595 984763 := bstep (se 1 (by rfl) ⟨738572, by rfl⟩ : syracuseStep 984763 = 1477145) B1477145
theorem B984839 : Blo 984595 984839 := bstep (se 1 (by rfl) ⟨738629, by rfl⟩ : syracuseStep 984839 = 1477259) B1477259
theorem B984847 : Blo 984595 984847 := bstep (se 1 (by rfl) ⟨738635, by rfl⟩ : syracuseStep 984847 = 1477271) B1477271
theorem B5998369 : Blo 984595 5998369 := bstep (se 2 (by rfl) ⟨2249388, by rfl⟩ : syracuseStep 5998369 = 4498777) B4498777
theorem B984891 : Blo 984595 984891 := bstep (se 1 (by rfl) ⟨738668, by rfl⟩ : syracuseStep 984891 = 1477337) B1477337
theorem B14419781 : Blo 984595 14419781 := bstep (se 4 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 14419781 = 2703709) B2703709
theorem B2492279 : Blo 984595 2492279 := bstep (se 1 (by rfl) ⟨1869209, by rfl⟩ : syracuseStep 2492279 = 3738419) B3738419
theorem B984967 : Blo 984595 984967 := bstep (se 1 (by rfl) ⟨738725, by rfl⟩ : syracuseStep 984967 = 1477451) B1477451
theorem B984975 : Blo 984595 984975 := bstep (se 1 (by rfl) ⟨738731, by rfl⟩ : syracuseStep 984975 = 1477463) B1477463
theorem B985019 : Blo 984595 985019 := bstep (se 1 (by rfl) ⟨738764, by rfl⟩ : syracuseStep 985019 = 1477529) B1477529
theorem B985095 : Blo 984595 985095 := bstep (se 1 (by rfl) ⟨738821, by rfl⟩ : syracuseStep 985095 = 1477643) B1477643
theorem B985103 : Blo 984595 985103 := bstep (se 1 (by rfl) ⟨738827, by rfl⟩ : syracuseStep 985103 = 1477655) B1477655
theorem B985147 : Blo 984595 985147 := bstep (se 1 (by rfl) ⟨738860, by rfl⟩ : syracuseStep 985147 = 1477721) B1477721
theorem B985223 : Blo 984595 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B985231 : Blo 984595 985231 := bstep (se 1 (by rfl) ⟨738923, by rfl⟩ : syracuseStep 985231 = 1477847) B1477847
theorem B985275 : Blo 984595 985275 := bstep (se 1 (by rfl) ⟨738956, by rfl⟩ : syracuseStep 985275 = 1477913) B1477913
theorem B985351 : Blo 984595 985351 := bstep (se 1 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 985351 = 1478027) B1478027
theorem B985359 : Blo 984595 985359 := bstep (se 1 (by rfl) ⟨739019, by rfl⟩ : syracuseStep 985359 = 1478039) B1478039
theorem B3377423 : Blo 984595 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B1476923 : Blo 984595 1476923 := bstep (se 1 (by rfl) ⟨1107692, by rfl⟩ : syracuseStep 1476923 = 2215385) B2215385
theorem B985403 : Blo 984595 985403 := bstep (se 1 (by rfl) ⟨739052, by rfl⟩ : syracuseStep 985403 = 1478105) B1478105
theorem B1476983 : Blo 984595 1476983 := bstep (se 1 (by rfl) ⟨1107737, by rfl⟩ : syracuseStep 1476983 = 2215475) B2215475
theorem B985479 : Blo 984595 985479 := bstep (se 1 (by rfl) ⟨739109, by rfl⟩ : syracuseStep 985479 = 1478219) B1478219
theorem B1477007 : Blo 984595 1477007 := bstep (se 1 (by rfl) ⟨1107755, by rfl⟩ : syracuseStep 1477007 = 2215511) B2215511
theorem B985487 : Blo 984595 985487 := bstep (se 1 (by rfl) ⟨739115, by rfl⟩ : syracuseStep 985487 = 1478231) B1478231
theorem B1477049 : Blo 984595 1477049 := bstep (se 2 (by rfl) ⟨553893, by rfl⟩ : syracuseStep 1477049 = 1107787) B1107787
theorem B1870265 : Blo 984595 1870265 := bstep (se 2 (by rfl) ⟨701349, by rfl⟩ : syracuseStep 1870265 = 1402699) B1402699
theorem B985531 : Blo 984595 985531 := bstep (se 1 (by rfl) ⟨739148, by rfl⟩ : syracuseStep 985531 = 1478297) B1478297
theorem B1477127 : Blo 984595 1477127 := bstep (se 1 (by rfl) ⟨1107845, by rfl⟩ : syracuseStep 1477127 = 2215691) B2215691
theorem B985607 : Blo 984595 985607 := bstep (se 1 (by rfl) ⟨739205, by rfl⟩ : syracuseStep 985607 = 1478411) B1478411
theorem B985615 : Blo 984595 985615 := bstep (se 1 (by rfl) ⟨739211, by rfl⟩ : syracuseStep 985615 = 1478423) B1478423
theorem B1477163 : Blo 984595 1477163 := bstep (se 1 (by rfl) ⟨1107872, by rfl⟩ : syracuseStep 1477163 = 2215745) B2215745
theorem B985659 : Blo 984595 985659 := bstep (se 1 (by rfl) ⟨739244, by rfl⟩ : syracuseStep 985659 = 1478489) B1478489
theorem B1477193 : Blo 984595 1477193 := bstep (se 2 (by rfl) ⟨553947, by rfl⟩ : syracuseStep 1477193 = 1107895) B1107895
theorem B985735 : Blo 984595 985735 := bstep (se 1 (by rfl) ⟨739301, by rfl⟩ : syracuseStep 985735 = 1478603) B1478603
theorem B985743 : Blo 984595 985743 := bstep (se 1 (by rfl) ⟨739307, by rfl⟩ : syracuseStep 985743 = 1478615) B1478615
theorem B1477307 : Blo 984595 1477307 := bstep (se 1 (by rfl) ⟨1107980, by rfl⟩ : syracuseStep 1477307 = 2215961) B2215961
theorem B985787 : Blo 984595 985787 := bstep (se 1 (by rfl) ⟨739340, by rfl⟩ : syracuseStep 985787 = 1478681) B1478681
theorem B1477367 : Blo 984595 1477367 := bstep (se 1 (by rfl) ⟨1108025, by rfl⟩ : syracuseStep 1477367 = 2216051) B2216051
theorem B985863 : Blo 984595 985863 := bstep (se 1 (by rfl) ⟨739397, by rfl⟩ : syracuseStep 985863 = 1478795) B1478795
theorem B1477391 : Blo 984595 1477391 := bstep (se 1 (by rfl) ⟨1108043, by rfl⟩ : syracuseStep 1477391 = 2216087) B2216087
theorem B1870607 : Blo 984595 1870607 := bstep (se 1 (by rfl) ⟨1402955, by rfl⟩ : syracuseStep 1870607 = 2805911) B2805911
theorem B985871 : Blo 984595 985871 := bstep (se 1 (by rfl) ⟨739403, by rfl⟩ : syracuseStep 985871 = 1478807) B1478807
theorem B1248043 : Blo 984595 1248043 := bstep (se 1 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 1248043 = 1872065) B1872065
theorem B1477433 : Blo 984595 1477433 := bstep (se 2 (by rfl) ⟨554037, by rfl⟩ : syracuseStep 1477433 = 1108075) B1108075
theorem B985915 : Blo 984595 985915 := bstep (se 1 (by rfl) ⟨739436, by rfl⟩ : syracuseStep 985915 = 1478873) B1478873
theorem B45484915 : Blo 984595 45484915 := bstep (se 1 (by rfl) ⟨34113686, by rfl⟩ : syracuseStep 45484915 = 68227373) B68227373
theorem B1477511 : Blo 984595 1477511 := bstep (se 1 (by rfl) ⟨1108133, by rfl⟩ : syracuseStep 1477511 = 2216267) B2216267
theorem B985991 : Blo 984595 985991 := bstep (se 1 (by rfl) ⟨739493, by rfl⟩ : syracuseStep 985991 = 1478987) B1478987
theorem B985999 : Blo 984595 985999 := bstep (se 1 (by rfl) ⟨739499, by rfl⟩ : syracuseStep 985999 = 1478999) B1478999
theorem B1477547 : Blo 984595 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B986043 : Blo 984595 986043 := bstep (se 1 (by rfl) ⟨739532, by rfl⟩ : syracuseStep 986043 = 1479065) B1479065
theorem B1477577 : Blo 984595 1477577 := bstep (se 2 (by rfl) ⟨554091, by rfl⟩ : syracuseStep 1477577 = 1108183) B1108183
theorem B986119 : Blo 984595 986119 := bstep (se 1 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 986119 = 1479179) B1479179
theorem B986127 : Blo 984595 986127 := bstep (se 1 (by rfl) ⟨739595, by rfl⟩ : syracuseStep 986127 = 1479191) B1479191
theorem B1477691 : Blo 984595 1477691 := bstep (se 1 (by rfl) ⟨1108268, by rfl⟩ : syracuseStep 1477691 = 2216537) B2216537
theorem B986171 : Blo 984595 986171 := bstep (se 1 (by rfl) ⟨739628, by rfl⟩ : syracuseStep 986171 = 1479257) B1479257
theorem B1477751 : Blo 984595 1477751 := bstep (se 1 (by rfl) ⟨1108313, by rfl⟩ : syracuseStep 1477751 = 2216627) B2216627
theorem B1805431 : Blo 984595 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B2493575 : Blo 984595 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B986247 : Blo 984595 986247 := bstep (se 1 (by rfl) ⟨739685, by rfl⟩ : syracuseStep 986247 = 1479371) B1479371
theorem B1477775 : Blo 984595 1477775 := bstep (se 1 (by rfl) ⟨1108331, by rfl⟩ : syracuseStep 1477775 = 2216663) B2216663
theorem B986255 : Blo 984595 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B40995989 : Blo 984595 40995989 := bstep (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) B1921687
theorem B2493625 : Blo 984595 2493625 := bstep (se 2 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 2493625 = 1870219) B1870219
theorem B1477817 : Blo 984595 1477817 := bstep (se 2 (by rfl) ⟨554181, by rfl⟩ : syracuseStep 1477817 = 1108363) B1108363
theorem B986299 : Blo 984595 986299 := bstep (se 1 (by rfl) ⟨739724, by rfl⟩ : syracuseStep 986299 = 1479449) B1479449
theorem B1477895 : Blo 984595 1477895 := bstep (se 1 (by rfl) ⟨1108421, by rfl⟩ : syracuseStep 1477895 = 2216843) B2216843
theorem B986375 : Blo 984595 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B2526479 : Blo 984595 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B986383 : Blo 984595 986383 := bstep (se 1 (by rfl) ⟨739787, by rfl⟩ : syracuseStep 986383 = 1479575) B1479575
theorem B1477931 : Blo 984595 1477931 := bstep (se 1 (by rfl) ⟨1108448, by rfl⟩ : syracuseStep 1477931 = 2216897) B2216897
theorem B986427 : Blo 984595 986427 := bstep (se 1 (by rfl) ⟨739820, by rfl⟩ : syracuseStep 986427 = 1479641) B1479641
theorem B1477961 : Blo 984595 1477961 := bstep (se 2 (by rfl) ⟨554235, by rfl⟩ : syracuseStep 1477961 = 1108471) B1108471
theorem B986503 : Blo 984595 986503 := bstep (se 1 (by rfl) ⟨739877, by rfl⟩ : syracuseStep 986503 = 1479755) B1479755
theorem B986511 : Blo 984595 986511 := bstep (se 1 (by rfl) ⟨739883, by rfl⟩ : syracuseStep 986511 = 1479767) B1479767
theorem B1478075 : Blo 984595 1478075 := bstep (se 1 (by rfl) ⟨1108556, by rfl⟩ : syracuseStep 1478075 = 2217113) B2217113
theorem B986555 : Blo 984595 986555 := bstep (se 1 (by rfl) ⟨739916, by rfl⟩ : syracuseStep 986555 = 1479833) B1479833
theorem B1478135 : Blo 984595 1478135 := bstep (se 1 (by rfl) ⟨1108601, by rfl⟩ : syracuseStep 1478135 = 2217203) B2217203
theorem B986631 : Blo 984595 986631 := bstep (se 1 (by rfl) ⟨739973, by rfl⟩ : syracuseStep 986631 = 1479947) B1479947
theorem B1478159 : Blo 984595 1478159 := bstep (se 1 (by rfl) ⟨1108619, by rfl⟩ : syracuseStep 1478159 = 2217239) B2217239
theorem B986639 : Blo 984595 986639 := bstep (se 1 (by rfl) ⟨739979, by rfl⟩ : syracuseStep 986639 = 1479959) B1479959
theorem B2002475 : Blo 984595 2002475 := bstep (se 1 (by rfl) ⟨1501856, by rfl⟩ : syracuseStep 2002475 = 3003713) B3003713
theorem B1478201 : Blo 984595 1478201 := bstep (se 2 (by rfl) ⟨554325, by rfl⟩ : syracuseStep 1478201 = 1108651) B1108651
theorem B1871419 : Blo 984595 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B986683 : Blo 984595 986683 := bstep (se 1 (by rfl) ⟨740012, by rfl⟩ : syracuseStep 986683 = 1480025) B1480025
theorem B3739223 : Blo 984595 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B1478279 : Blo 984595 1478279 := bstep (se 1 (by rfl) ⟨1108709, by rfl⟩ : syracuseStep 1478279 = 2217419) B2217419
theorem B1871495 : Blo 984595 1871495 := bstep (se 1 (by rfl) ⟨1403621, by rfl⟩ : syracuseStep 1871495 = 2807243) B2807243
theorem B986759 : Blo 984595 986759 := bstep (se 1 (by rfl) ⟨740069, by rfl⟩ : syracuseStep 986759 = 1480139) B1480139
theorem B986767 : Blo 984595 986767 := bstep (se 1 (by rfl) ⟨740075, by rfl⟩ : syracuseStep 986767 = 1480151) B1480151
theorem B1478315 : Blo 984595 1478315 := bstep (se 1 (by rfl) ⟨1108736, by rfl⟩ : syracuseStep 1478315 = 2217473) B2217473
theorem B986811 : Blo 984595 986811 := bstep (se 1 (by rfl) ⟨740108, by rfl⟩ : syracuseStep 986811 = 1480217) B1480217
theorem B1478345 : Blo 984595 1478345 := bstep (se 2 (by rfl) ⟨554379, by rfl⟩ : syracuseStep 1478345 = 1108759) B1108759
theorem B1249015 : Blo 984595 1249015 := bstep (se 1 (by rfl) ⟨936761, by rfl⟩ : syracuseStep 1249015 = 1873523) B1873523
theorem B4984577 : Blo 984595 4984577 := bstep (se 2 (by rfl) ⟨1869216, by rfl⟩ : syracuseStep 4984577 = 3738433) B3738433
theorem B986887 : Blo 984595 986887 := bstep (se 1 (by rfl) ⟨740165, by rfl⟩ : syracuseStep 986887 = 1480331) B1480331
theorem B2494223 : Blo 984595 2494223 := bstep (se 1 (by rfl) ⟨1870667, by rfl⟩ : syracuseStep 2494223 = 3741335) B3741335
theorem B986895 : Blo 984595 986895 := bstep (se 1 (by rfl) ⟨740171, by rfl⟩ : syracuseStep 986895 = 1480343) B1480343
theorem B1478459 : Blo 984595 1478459 := bstep (se 1 (by rfl) ⟨1108844, by rfl⟩ : syracuseStep 1478459 = 2217689) B2217689
theorem B986939 : Blo 984595 986939 := bstep (se 1 (by rfl) ⟨740204, by rfl⟩ : syracuseStep 986939 = 1480409) B1480409
theorem B7409497 : Blo 984595 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B1478519 : Blo 984595 1478519 := bstep (se 1 (by rfl) ⟨1108889, by rfl⟩ : syracuseStep 1478519 = 2217779) B2217779
theorem B987015 : Blo 984595 987015 := bstep (se 1 (by rfl) ⟨740261, by rfl⟩ : syracuseStep 987015 = 1480523) B1480523
theorem B2002823 : Blo 984595 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B1478543 : Blo 984595 1478543 := bstep (se 1 (by rfl) ⟨1108907, by rfl⟩ : syracuseStep 1478543 = 2217815) B2217815
theorem B987023 : Blo 984595 987023 := bstep (se 1 (by rfl) ⟨740267, by rfl⟩ : syracuseStep 987023 = 1480535) B1480535
theorem B1478585 : Blo 984595 1478585 := bstep (se 2 (by rfl) ⟨554469, by rfl⟩ : syracuseStep 1478585 = 1108939) B1108939
theorem B987067 : Blo 984595 987067 := bstep (se 1 (by rfl) ⟨740300, by rfl⟩ : syracuseStep 987067 = 1480601) B1480601
theorem B7606219 : Blo 984595 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B1478663 : Blo 984595 1478663 := bstep (se 1 (by rfl) ⟨1108997, by rfl⟩ : syracuseStep 1478663 = 2217995) B2217995
theorem B987143 : Blo 984595 987143 := bstep (se 1 (by rfl) ⟨740357, by rfl⟩ : syracuseStep 987143 = 1480715) B1480715
theorem B987151 : Blo 984595 987151 := bstep (se 1 (by rfl) ⟨740363, by rfl⟩ : syracuseStep 987151 = 1480727) B1480727
theorem B3379229 : Blo 984595 3379229 := bstep (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) B1267211
theorem B1871905 : Blo 984595 1871905 := bstep (se 2 (by rfl) ⟨701964, by rfl⟩ : syracuseStep 1871905 = 1403929) B1403929
theorem B1478699 : Blo 984595 1478699 := bstep (se 1 (by rfl) ⟨1109024, by rfl⟩ : syracuseStep 1478699 = 2218049) B2218049
theorem B1249339 : Blo 984595 1249339 := bstep (se 1 (by rfl) ⟨937004, by rfl⟩ : syracuseStep 1249339 = 1874009) B1874009
theorem B987195 : Blo 984595 987195 := bstep (se 1 (by rfl) ⟨740396, by rfl⟩ : syracuseStep 987195 = 1480793) B1480793
theorem B3739709 : Blo 984595 3739709 := bstep (se 3 (by rfl) ⟨701195, by rfl⟩ : syracuseStep 3739709 = 1402391) B1402391
theorem B1478729 : Blo 984595 1478729 := bstep (se 2 (by rfl) ⟨554523, by rfl⟩ : syracuseStep 1478729 = 1109047) B1109047
theorem B987271 : Blo 984595 987271 := bstep (se 1 (by rfl) ⟨740453, by rfl⟩ : syracuseStep 987271 = 1480907) B1480907
theorem B987279 : Blo 984595 987279 := bstep (se 1 (by rfl) ⟨740459, by rfl⟩ : syracuseStep 987279 = 1480919) B1480919
theorem B1478843 : Blo 984595 1478843 := bstep (se 1 (by rfl) ⟨1109132, by rfl⟩ : syracuseStep 1478843 = 2218265) B2218265
theorem B987323 : Blo 984595 987323 := bstep (se 1 (by rfl) ⟨740492, by rfl⟩ : syracuseStep 987323 = 1480985) B1480985
theorem B1478903 : Blo 984595 1478903 := bstep (se 1 (by rfl) ⟨1109177, by rfl⟩ : syracuseStep 1478903 = 2218355) B2218355
theorem B987399 : Blo 984595 987399 := bstep (se 1 (by rfl) ⟨740549, by rfl⟩ : syracuseStep 987399 = 1481099) B1481099
theorem B1478927 : Blo 984595 1478927 := bstep (se 1 (by rfl) ⟨1109195, by rfl⟩ : syracuseStep 1478927 = 2218391) B2218391
theorem B987407 : Blo 984595 987407 := bstep (se 1 (by rfl) ⟨740555, by rfl⟩ : syracuseStep 987407 = 1481111) B1481111
theorem B1478969 : Blo 984595 1478969 := bstep (se 2 (by rfl) ⟨554613, by rfl⟩ : syracuseStep 1478969 = 1109227) B1109227
theorem B987451 : Blo 984595 987451 := bstep (se 1 (by rfl) ⟨740588, by rfl⟩ : syracuseStep 987451 = 1481177) B1481177
theorem B1872247 : Blo 984595 1872247 := bstep (se 1 (by rfl) ⟨1404185, by rfl⟩ : syracuseStep 1872247 = 2808371) B2808371
theorem B1577351 : Blo 984595 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B1479047 : Blo 984595 1479047 := bstep (se 1 (by rfl) ⟨1109285, by rfl⟩ : syracuseStep 1479047 = 2218571) B2218571
theorem B987527 : Blo 984595 987527 := bstep (se 1 (by rfl) ⟨740645, by rfl⟩ : syracuseStep 987527 = 1481291) B1481291
theorem B987535 : Blo 984595 987535 := bstep (se 1 (by rfl) ⟨740651, by rfl⟩ : syracuseStep 987535 = 1481303) B1481303
theorem B1479083 : Blo 984595 1479083 := bstep (se 1 (by rfl) ⟨1109312, by rfl⟩ : syracuseStep 1479083 = 2218625) B2218625
theorem B987579 : Blo 984595 987579 := bstep (se 1 (by rfl) ⟨740684, by rfl⟩ : syracuseStep 987579 = 1481369) B1481369
theorem B2494921 : Blo 984595 2494921 := bstep (se 2 (by rfl) ⟨935595, by rfl⟩ : syracuseStep 2494921 = 1871191) B1871191
theorem B1479113 : Blo 984595 1479113 := bstep (se 2 (by rfl) ⟨554667, by rfl⟩ : syracuseStep 1479113 = 1109335) B1109335
theorem B987655 : Blo 984595 987655 := bstep (se 1 (by rfl) ⟨740741, by rfl⟩ : syracuseStep 987655 = 1481483) B1481483
theorem B987663 : Blo 984595 987663 := bstep (se 1 (by rfl) ⟨740747, by rfl⟩ : syracuseStep 987663 = 1481495) B1481495
theorem B4985387 : Blo 984595 4985387 := bstep (se 1 (by rfl) ⟨3739040, by rfl⟩ : syracuseStep 4985387 = 7478081) B7478081
theorem B1479227 : Blo 984595 1479227 := bstep (se 1 (by rfl) ⟨1109420, by rfl⟩ : syracuseStep 1479227 = 2218841) B2218841
theorem B987707 : Blo 984595 987707 := bstep (se 1 (by rfl) ⟨740780, by rfl⟩ : syracuseStep 987707 = 1481561) B1481561
theorem B2495063 : Blo 984595 2495063 := bstep (se 1 (by rfl) ⟨1871297, by rfl⟩ : syracuseStep 2495063 = 3742595) B3742595
theorem B1479287 : Blo 984595 1479287 := bstep (se 1 (by rfl) ⟨1109465, by rfl⟩ : syracuseStep 1479287 = 2218931) B2218931
theorem B987783 : Blo 984595 987783 := bstep (se 1 (by rfl) ⟨740837, by rfl⟩ : syracuseStep 987783 = 1481675) B1481675
theorem B1479311 : Blo 984595 1479311 := bstep (se 1 (by rfl) ⟨1109483, by rfl⟩ : syracuseStep 1479311 = 2218967) B2218967
theorem B987791 : Blo 984595 987791 := bstep (se 1 (by rfl) ⟨740843, by rfl⟩ : syracuseStep 987791 = 1481687) B1481687
theorem B1479353 : Blo 984595 1479353 := bstep (se 2 (by rfl) ⟨554757, by rfl⟩ : syracuseStep 1479353 = 1109515) B1109515
theorem B987835 : Blo 984595 987835 := bstep (se 1 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 987835 = 1481753) B1481753
theorem B1479431 : Blo 984595 1479431 := bstep (se 1 (by rfl) ⟨1109573, by rfl⟩ : syracuseStep 1479431 = 2219147) B2219147
theorem B987911 : Blo 984595 987911 := bstep (se 1 (by rfl) ⟨740933, by rfl⟩ : syracuseStep 987911 = 1481867) B1481867
theorem B987919 : Blo 984595 987919 := bstep (se 1 (by rfl) ⟨740939, by rfl⟩ : syracuseStep 987919 = 1481879) B1481879
theorem B1479467 : Blo 984595 1479467 := bstep (se 1 (by rfl) ⟨1109600, by rfl⟩ : syracuseStep 1479467 = 2219201) B2219201
theorem B987963 : Blo 984595 987963 := bstep (se 1 (by rfl) ⟨740972, by rfl⟩ : syracuseStep 987963 = 1481945) B1481945
theorem B1479497 : Blo 984595 1479497 := bstep (se 2 (by rfl) ⟨554811, by rfl⟩ : syracuseStep 1479497 = 1109623) B1109623
theorem B988039 : Blo 984595 988039 := bstep (se 1 (by rfl) ⟨741029, by rfl⟩ : syracuseStep 988039 = 1482059) B1482059
theorem B988047 : Blo 984595 988047 := bstep (se 1 (by rfl) ⟨741035, by rfl⟩ : syracuseStep 988047 = 1482071) B1482071
theorem B1479611 : Blo 984595 1479611 := bstep (se 1 (by rfl) ⟨1109708, by rfl⟩ : syracuseStep 1479611 = 2219417) B2219417
theorem B988091 : Blo 984595 988091 := bstep (se 1 (by rfl) ⟨741068, by rfl⟩ : syracuseStep 988091 = 1482137) B1482137
theorem B1479671 : Blo 984595 1479671 := bstep (se 1 (by rfl) ⟨1109753, by rfl⟩ : syracuseStep 1479671 = 2219507) B2219507
theorem B1250311 : Blo 984595 1250311 := bstep (se 1 (by rfl) ⟨937733, by rfl⟩ : syracuseStep 1250311 = 1875467) B1875467
theorem B988167 : Blo 984595 988167 := bstep (se 1 (by rfl) ⟨741125, by rfl⟩ : syracuseStep 988167 = 1482251) B1482251
theorem B1479695 : Blo 984595 1479695 := bstep (se 1 (by rfl) ⟨1109771, by rfl⟩ : syracuseStep 1479695 = 2219543) B2219543
theorem B988175 : Blo 984595 988175 := bstep (se 1 (by rfl) ⟨741131, by rfl⟩ : syracuseStep 988175 = 1482263) B1482263
theorem B1479737 : Blo 984595 1479737 := bstep (se 2 (by rfl) ⟨554901, by rfl⟩ : syracuseStep 1479737 = 1109803) B1109803
theorem B988219 : Blo 984595 988219 := bstep (se 1 (by rfl) ⟨741164, by rfl⟩ : syracuseStep 988219 = 1482329) B1482329
theorem B1479815 : Blo 984595 1479815 := bstep (se 1 (by rfl) ⟨1109861, by rfl⟩ : syracuseStep 1479815 = 2219723) B2219723
theorem B988295 : Blo 984595 988295 := bstep (se 1 (by rfl) ⟨741221, by rfl⟩ : syracuseStep 988295 = 1482443) B1482443
theorem B988303 : Blo 984595 988303 := bstep (se 1 (by rfl) ⟨741227, by rfl⟩ : syracuseStep 988303 = 1482455) B1482455
theorem B1479851 : Blo 984595 1479851 := bstep (se 1 (by rfl) ⟨1109888, by rfl⟩ : syracuseStep 1479851 = 2219777) B2219777
theorem B988347 : Blo 984595 988347 := bstep (se 1 (by rfl) ⟨741260, by rfl⟩ : syracuseStep 988347 = 1482521) B1482521
theorem B1479881 : Blo 984595 1479881 := bstep (se 2 (by rfl) ⟨554955, by rfl⟩ : syracuseStep 1479881 = 1109911) B1109911
theorem B10687733 : Blo 984595 10687733 := bstep (se 5 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 10687733 = 1001975) B1001975
theorem B988423 : Blo 984595 988423 := bstep (se 1 (by rfl) ⟨741317, by rfl⟩ : syracuseStep 988423 = 1482635) B1482635
theorem B988431 : Blo 984595 988431 := bstep (se 1 (by rfl) ⟨741323, by rfl⟩ : syracuseStep 988431 = 1482647) B1482647
theorem B1479995 : Blo 984595 1479995 := bstep (se 1 (by rfl) ⟨1109996, by rfl⟩ : syracuseStep 1479995 = 2219993) B2219993
theorem B988475 : Blo 984595 988475 := bstep (se 1 (by rfl) ⟨741356, by rfl⟩ : syracuseStep 988475 = 1482713) B1482713
theorem B1480055 : Blo 984595 1480055 := bstep (se 1 (by rfl) ⟨1110041, by rfl⟩ : syracuseStep 1480055 = 2220083) B2220083
theorem B988551 : Blo 984595 988551 := bstep (se 1 (by rfl) ⟨741413, by rfl⟩ : syracuseStep 988551 = 1482827) B1482827
theorem B1480079 : Blo 984595 1480079 := bstep (se 1 (by rfl) ⟨1110059, by rfl⟩ : syracuseStep 1480079 = 2220119) B2220119
theorem B988559 : Blo 984595 988559 := bstep (se 1 (by rfl) ⟨741419, by rfl⟩ : syracuseStep 988559 = 1482839) B1482839
theorem B1250731 : Blo 984595 1250731 := bstep (se 1 (by rfl) ⟨938048, by rfl⟩ : syracuseStep 1250731 = 1876097) B1876097
theorem B1480121 : Blo 984595 1480121 := bstep (se 2 (by rfl) ⟨555045, by rfl⟩ : syracuseStep 1480121 = 1110091) B1110091
theorem B3741137 : Blo 984595 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B1480199 : Blo 984595 1480199 := bstep (se 1 (by rfl) ⟨1110149, by rfl⟩ : syracuseStep 1480199 = 2220299) B2220299
theorem B1480235 : Blo 984595 1480235 := bstep (se 1 (by rfl) ⟨1110176, by rfl⟩ : syracuseStep 1480235 = 2220353) B2220353
theorem B1480265 : Blo 984595 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B1250959 : Blo 984595 1250959 := bstep (se 1 (by rfl) ⟨938219, by rfl⟩ : syracuseStep 1250959 = 1876439) B1876439
theorem B1480379 : Blo 984595 1480379 := bstep (se 1 (by rfl) ⟨1110284, by rfl⟩ : syracuseStep 1480379 = 2220569) B2220569
theorem B1480439 : Blo 984595 1480439 := bstep (se 1 (by rfl) ⟨1110329, by rfl⟩ : syracuseStep 1480439 = 2220659) B2220659
theorem B1480463 : Blo 984595 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B1480505 : Blo 984595 1480505 := bstep (se 2 (by rfl) ⟨555189, by rfl⟩ : syracuseStep 1480505 = 1110379) B1110379
theorem B4986683 : Blo 984595 4986683 := bstep (se 1 (by rfl) ⟨3740012, by rfl⟩ : syracuseStep 4986683 = 7480025) B7480025
theorem B7313267 : Blo 984595 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B1480583 : Blo 984595 1480583 := bstep (se 1 (by rfl) ⟨1110437, by rfl⟩ : syracuseStep 1480583 = 2220875) B2220875
theorem B1480619 : Blo 984595 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B1873849 : Blo 984595 1873849 := bstep (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) B1405387
theorem B1480649 : Blo 984595 1480649 := bstep (se 2 (by rfl) ⟨555243, by rfl⟩ : syracuseStep 1480649 = 1110487) B1110487
theorem B4986845 : Blo 984595 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B21305389 : Blo 984595 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B1480763 : Blo 984595 1480763 := bstep (se 1 (by rfl) ⟨1110572, by rfl⟩ : syracuseStep 1480763 = 2221145) B2221145
theorem B1480823 : Blo 984595 1480823 := bstep (se 1 (by rfl) ⟨1110617, by rfl⟩ : syracuseStep 1480823 = 2221235) B2221235
theorem B1185935 : Blo 984595 1185935 := bstep (se 1 (by rfl) ⟨889451, by rfl⟩ : syracuseStep 1185935 = 1778903) B1778903
theorem B1480847 : Blo 984595 1480847 := bstep (se 1 (by rfl) ⟨1110635, by rfl⟩ : syracuseStep 1480847 = 2221271) B2221271
theorem B1480889 : Blo 984595 1480889 := bstep (se 2 (by rfl) ⟨555333, by rfl⟩ : syracuseStep 1480889 = 1110667) B1110667
theorem B1480967 : Blo 984595 1480967 := bstep (se 1 (by rfl) ⟨1110725, by rfl⟩ : syracuseStep 1480967 = 2221451) B2221451
theorem B1874191 : Blo 984595 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B4987169 : Blo 984595 4987169 := bstep (se 2 (by rfl) ⟨1870188, by rfl⟩ : syracuseStep 4987169 = 3740377) B3740377
theorem B1481003 : Blo 984595 1481003 := bstep (se 1 (by rfl) ⟨1110752, by rfl⟩ : syracuseStep 1481003 = 2221505) B2221505
theorem B1481033 : Blo 984595 1481033 := bstep (se 2 (by rfl) ⟨555387, by rfl⟩ : syracuseStep 1481033 = 1110775) B1110775
theorem B1481147 : Blo 984595 1481147 := bstep (se 1 (by rfl) ⟨1110860, by rfl⟩ : syracuseStep 1481147 = 2221721) B2221721
theorem B1481207 : Blo 984595 1481207 := bstep (se 1 (by rfl) ⟨1110905, by rfl⟩ : syracuseStep 1481207 = 2221811) B2221811
theorem B4004363 : Blo 984595 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B1481231 : Blo 984595 1481231 := bstep (se 1 (by rfl) ⟨1110923, by rfl⟩ : syracuseStep 1481231 = 2221847) B2221847
theorem B1481273 : Blo 984595 1481273 := bstep (se 2 (by rfl) ⟨555477, by rfl⟩ : syracuseStep 1481273 = 1110955) B1110955
theorem B2497139 : Blo 984595 2497139 := bstep (se 1 (by rfl) ⟨1872854, by rfl⟩ : syracuseStep 2497139 = 3745709) B3745709
theorem B8428151 : Blo 984595 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B1481351 : Blo 984595 1481351 := bstep (se 1 (by rfl) ⟨1111013, by rfl⟩ : syracuseStep 1481351 = 2222027) B2222027
theorem B1186439 : Blo 984595 1186439 := bstep (se 1 (by rfl) ⟨889829, by rfl⟩ : syracuseStep 1186439 = 1779659) B1779659
theorem B1481387 : Blo 984595 1481387 := bstep (se 1 (by rfl) ⟨1111040, by rfl⟩ : syracuseStep 1481387 = 2222081) B2222081
theorem B1481417 : Blo 984595 1481417 := bstep (se 2 (by rfl) ⟨555531, by rfl⟩ : syracuseStep 1481417 = 1111063) B1111063
theorem B2366209 : Blo 984595 2366209 := bstep (se 2 (by rfl) ⟨887328, by rfl⟩ : syracuseStep 2366209 = 1774657) B1774657
theorem B1481531 : Blo 984595 1481531 := bstep (se 1 (by rfl) ⟨1111148, by rfl⟩ : syracuseStep 1481531 = 2222297) B2222297
theorem B1579895 : Blo 984595 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B1481591 : Blo 984595 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1481615 : Blo 984595 1481615 := bstep (se 1 (by rfl) ⟨1111211, by rfl⟩ : syracuseStep 1481615 = 2222423) B2222423
theorem B1481657 : Blo 984595 1481657 := bstep (se 2 (by rfl) ⟨555621, by rfl⟩ : syracuseStep 1481657 = 1111243) B1111243
theorem B17538053 : Blo 984595 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B1481735 : Blo 984595 1481735 := bstep (se 1 (by rfl) ⟨1111301, by rfl⟩ : syracuseStep 1481735 = 2222603) B2222603
theorem B1481771 : Blo 984595 1481771 := bstep (se 1 (by rfl) ⟨1111328, by rfl⟩ : syracuseStep 1481771 = 2222657) B2222657
theorem B1481801 : Blo 984595 1481801 := bstep (se 2 (by rfl) ⟨555675, by rfl⟩ : syracuseStep 1481801 = 1111351) B1111351
theorem B3742807 : Blo 984595 3742807 := bstep (se 1 (by rfl) ⟨2807105, by rfl⟩ : syracuseStep 3742807 = 5614211) B5614211
theorem B2497655 : Blo 984595 2497655 := bstep (se 1 (by rfl) ⟨1873241, by rfl⟩ : syracuseStep 2497655 = 3746483) B3746483
theorem B1875079 : Blo 984595 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B1481915 : Blo 984595 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B4988141 : Blo 984595 4988141 := bstep (se 3 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 4988141 = 1870553) B1870553
theorem B1481975 : Blo 984595 1481975 := bstep (se 1 (by rfl) ⟨1111481, by rfl⟩ : syracuseStep 1481975 = 2222963) B2222963
theorem B1481999 : Blo 984595 1481999 := bstep (se 1 (by rfl) ⟨1111499, by rfl⟩ : syracuseStep 1481999 = 2222999) B2222999
theorem B1482041 : Blo 984595 1482041 := bstep (se 2 (by rfl) ⟨555765, by rfl⟩ : syracuseStep 1482041 = 1111531) B1111531
theorem B3743111 : Blo 984595 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B1482119 : Blo 984595 1482119 := bstep (se 1 (by rfl) ⟨1111589, by rfl⟩ : syracuseStep 1482119 = 2223179) B2223179
theorem B1482155 : Blo 984595 1482155 := bstep (se 1 (by rfl) ⟨1111616, by rfl⟩ : syracuseStep 1482155 = 2223233) B2223233
theorem B1482185 : Blo 984595 1482185 := bstep (se 2 (by rfl) ⟨555819, by rfl⟩ : syracuseStep 1482185 = 1111639) B1111639
theorem B1482299 : Blo 984595 1482299 := bstep (se 1 (by rfl) ⟨1111724, by rfl⟩ : syracuseStep 1482299 = 2223449) B2223449
theorem B3743293 : Blo 984595 3743293 := bstep (se 3 (by rfl) ⟨701867, by rfl⟩ : syracuseStep 3743293 = 1403735) B1403735
theorem B1482359 : Blo 984595 1482359 := bstep (se 1 (by rfl) ⟨1111769, by rfl⟩ : syracuseStep 1482359 = 2223539) B2223539
theorem B1482383 : Blo 984595 1482383 := bstep (se 1 (by rfl) ⟨1111787, by rfl⟩ : syracuseStep 1482383 = 2223575) B2223575
theorem B1482425 : Blo 984595 1482425 := bstep (se 2 (by rfl) ⟨555909, by rfl⟩ : syracuseStep 1482425 = 1111819) B1111819
theorem B1482503 : Blo 984595 1482503 := bstep (se 1 (by rfl) ⟨1111877, by rfl⟩ : syracuseStep 1482503 = 2223755) B2223755
theorem B1580843 : Blo 984595 1580843 := bstep (se 1 (by rfl) ⟨1185632, by rfl⟩ : syracuseStep 1580843 = 2371265) B2371265
theorem B1482539 : Blo 984595 1482539 := bstep (se 1 (by rfl) ⟨1111904, by rfl⟩ : syracuseStep 1482539 = 2223809) B2223809
theorem B1482569 : Blo 984595 1482569 := bstep (se 2 (by rfl) ⟨555963, by rfl⟩ : syracuseStep 1482569 = 1111927) B1111927
theorem B1777555 : Blo 984595 1777555 := bstep (se 1 (by rfl) ⟨1333166, by rfl⟩ : syracuseStep 1777555 = 2666333) B2666333
theorem B5054393 : Blo 984595 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1482683 : Blo 984595 1482683 := bstep (se 1 (by rfl) ⟨1112012, by rfl⟩ : syracuseStep 1482683 = 2224025) B2224025
theorem B1482743 : Blo 984595 1482743 := bstep (se 1 (by rfl) ⟨1112057, by rfl⟩ : syracuseStep 1482743 = 2224115) B2224115
theorem B1482767 : Blo 984595 1482767 := bstep (se 1 (by rfl) ⟨1112075, by rfl⟩ : syracuseStep 1482767 = 2224151) B2224151
theorem B4988951 : Blo 984595 4988951 := bstep (se 1 (by rfl) ⟨3741713, by rfl⟩ : syracuseStep 4988951 = 7483427) B7483427
theorem B1482809 : Blo 984595 1482809 := bstep (se 2 (by rfl) ⟨556053, by rfl⟩ : syracuseStep 1482809 = 1112107) B1112107
theorem B2498647 : Blo 984595 2498647 := bstep (se 1 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 2498647 = 3747971) B3747971
theorem B1482887 : Blo 984595 1482887 := bstep (se 1 (by rfl) ⟨1112165, by rfl⟩ : syracuseStep 1482887 = 2224331) B2224331
theorem B1351927 : Blo 984595 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B2498951 : Blo 984595 2498951 := bstep (se 1 (by rfl) ⟨1874213, by rfl⟩ : syracuseStep 2498951 = 3748427) B3748427
theorem B2499083 : Blo 984595 2499083 := bstep (se 1 (by rfl) ⟨1874312, by rfl⟩ : syracuseStep 2499083 = 3748625) B3748625
theorem B16228907 : Blo 984595 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B1581611 : Blo 984595 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B23372659 : Blo 984595 23372659 := bstep (se 1 (by rfl) ⟨17529494, by rfl⟩ : syracuseStep 23372659 = 35058989) B35058989
theorem B5612435 : Blo 984595 5612435 := bstep (se 1 (by rfl) ⟨4209326, by rfl⟩ : syracuseStep 5612435 = 8418653) B8418653
theorem B2499599 : Blo 984595 2499599 := bstep (se 1 (by rfl) ⟨1874699, by rfl⟩ : syracuseStep 2499599 = 3749399) B3749399
theorem B59352139 : Blo 984595 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B2499731 : Blo 984595 2499731 := bstep (se 1 (by rfl) ⟨1874798, by rfl⟩ : syracuseStep 2499731 = 3749597) B3749597
theorem B3745025 : Blo 984595 3745025 := bstep (se 2 (by rfl) ⟨1404384, by rfl⟩ : syracuseStep 3745025 = 2808769) B2808769
theorem B5612935 : Blo 984595 5612935 := bstep (se 1 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 5612935 = 8419403) B8419403
theorem B2139527 : Blo 984595 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B2664083 : Blo 984595 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B1779401 : Blo 984595 1779401 := bstep (se 2 (by rfl) ⟨667275, by rfl⟩ : syracuseStep 1779401 = 1334551) B1334551
theorem B4499201 : Blo 984595 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B2664377 : Blo 984595 2664377 := bstep (se 2 (by rfl) ⟨999141, by rfl⟩ : syracuseStep 2664377 = 1998283) B1998283
theorem B6006737 : Blo 984595 6006737 := bstep (se 2 (by rfl) ⟨2252526, by rfl⟩ : syracuseStep 6006737 = 4505053) B4505053
theorem B2500865 : Blo 984595 2500865 := bstep (se 2 (by rfl) ⟨937824, by rfl⟩ : syracuseStep 2500865 = 1875649) B1875649
theorem B2369803 : Blo 984595 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B3746195 : Blo 984595 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B2107919 : Blo 984595 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B3156509 : Blo 984595 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B2501239 : Blo 984595 2501239 := bstep (se 1 (by rfl) ⟨1875929, by rfl⟩ : syracuseStep 2501239 = 3751859) B3751859
theorem B11414135 : Blo 984595 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B3746695 : Blo 984595 3746695 := bstep (se 1 (by rfl) ⟨2810021, by rfl⟩ : syracuseStep 3746695 = 5620043) B5620043
theorem B4992029 : Blo 984595 4992029 := bstep (se 3 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 4992029 = 1872011) B1872011
theorem B2501675 : Blo 984595 2501675 := bstep (se 1 (by rfl) ⟨1876256, by rfl⟩ : syracuseStep 2501675 = 3752513) B3752513
theorem B7482455 : Blo 984595 7482455 := bstep (se 1 (by rfl) ⟨5611841, by rfl⟩ : syracuseStep 7482455 = 11223683) B11223683
theorem B4992515 : Blo 984595 4992515 := bstep (se 1 (by rfl) ⟨3744386, by rfl⟩ : syracuseStep 4992515 = 7488773) B7488773
theorem B14233117 : Blo 984595 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B2666375 : Blo 984595 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B9482285 : Blo 984595 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B2109559 : Blo 984595 2109559 := bstep (se 1 (by rfl) ⟨1582169, by rfl⟩ : syracuseStep 2109559 = 3164339) B3164339
theorem B2470297 : Blo 984595 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B22819313 : Blo 984595 22819313 := bstep (se 2 (by rfl) ⟨8557242, by rfl⟩ : syracuseStep 22819313 = 17114485) B17114485
theorem B4994135 : Blo 984595 4994135 := bstep (se 1 (by rfl) ⟨3745601, by rfl⟩ : syracuseStep 4994135 = 7491203) B7491203
theorem B2995319 : Blo 984595 2995319 := bstep (se 1 (by rfl) ⟨2246489, by rfl⟩ : syracuseStep 2995319 = 4492979) B4492979
theorem B3323321 : Blo 984595 3323321 := bstep (se 2 (by rfl) ⟨1246245, by rfl⟩ : syracuseStep 3323321 = 2492491) B2492491
theorem B3159481 : Blo 984595 3159481 := bstep (se 2 (by rfl) ⟨1184805, by rfl⟩ : syracuseStep 3159481 = 2369611) B2369611
theorem B4994621 : Blo 984595 4994621 := bstep (se 3 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 4994621 = 1872983) B1872983
theorem B6010487 : Blo 984595 6010487 := bstep (se 1 (by rfl) ⟨4507865, by rfl⟩ : syracuseStep 6010487 = 9015731) B9015731
theorem B2111275 : Blo 984595 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B18003863 : Blo 984595 18003863 := bstep (se 1 (by rfl) ⟨13502897, by rfl⟩ : syracuseStep 18003863 = 27005795) B27005795
theorem B3323915 : Blo 984595 3323915 := bstep (se 1 (by rfl) ⟨2492936, by rfl⟩ : syracuseStep 3323915 = 4985873) B4985873
theorem B3324023 : Blo 984595 3324023 := bstep (se 1 (by rfl) ⟨2493017, by rfl⟩ : syracuseStep 3324023 = 4986035) B4986035
theorem B4503671 : Blo 984595 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B9124013 : Blo 984595 9124013 := bstep (se 3 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 9124013 = 3421505) B3421505
theorem B7125383 : Blo 984595 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B11254301 : Blo 984595 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B2996851 : Blo 984595 2996851 := bstep (se 1 (by rfl) ⟨2247638, by rfl⟩ : syracuseStep 2996851 = 4495277) B4495277
theorem B3324617 : Blo 984595 3324617 := bstep (se 2 (by rfl) ⟨1246731, by rfl⟩ : syracuseStep 3324617 = 2493463) B2493463
theorem B3160865 : Blo 984595 3160865 := bstep (se 2 (by rfl) ⟨1185324, by rfl⟩ : syracuseStep 3160865 = 2370649) B2370649
theorem B4733747 : Blo 984595 4733747 := bstep (se 1 (by rfl) ⟨3550310, by rfl⟩ : syracuseStep 4733747 = 7100621) B7100621
theorem B5618585 : Blo 984595 5618585 := bstep (se 2 (by rfl) ⟨2106969, by rfl⟩ : syracuseStep 5618585 = 4213939) B4213939
theorem B2374667 : Blo 984595 2374667 := bstep (se 1 (by rfl) ⟨1781000, by rfl⟩ : syracuseStep 2374667 = 3562001) B3562001
theorem B4734071 : Blo 984595 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B3161377 : Blo 984595 3161377 := bstep (se 2 (by rfl) ⟨1185516, by rfl⟩ : syracuseStep 3161377 = 2371033) B2371033
theorem B4996403 : Blo 984595 4996403 := bstep (se 1 (by rfl) ⟨3747302, by rfl⟩ : syracuseStep 4996403 = 7494605) B7494605
theorem B3325319 : Blo 984595 3325319 := bstep (se 1 (by rfl) ⟨2493989, by rfl⟩ : syracuseStep 3325319 = 4987979) B4987979
theorem B8994347 : Blo 984595 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B4996727 : Blo 984595 4996727 := bstep (se 1 (by rfl) ⟨3747545, by rfl⟩ : syracuseStep 4996727 = 7495091) B7495091
theorem B3325697 : Blo 984595 3325697 := bstep (se 2 (by rfl) ⟨1247136, by rfl⟩ : syracuseStep 3325697 = 2494273) B2494273
theorem B14204747 : Blo 984595 14204747 := bstep (se 1 (by rfl) ⟨10653560, by rfl⟩ : syracuseStep 14204747 = 21307121) B21307121
theorem B10665931 : Blo 984595 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B2670635 : Blo 984595 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B3752345 : Blo 984595 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B3162635 : Blo 984595 3162635 := bstep (se 1 (by rfl) ⟨2371976, by rfl⟩ : syracuseStep 3162635 = 4743953) B4743953
theorem B3326507 : Blo 984595 3326507 := bstep (se 1 (by rfl) ⟨2494880, by rfl⟩ : syracuseStep 3326507 = 4989761) B4989761
theorem B4997699 : Blo 984595 4997699 := bstep (se 1 (by rfl) ⟨3748274, by rfl⟩ : syracuseStep 4997699 = 7496549) B7496549
theorem B4735745 : Blo 984595 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B4998023 : Blo 984595 4998023 := bstep (se 1 (by rfl) ⟨3748517, by rfl⟩ : syracuseStep 4998023 = 7497035) B7497035
theorem B4506553 : Blo 984595 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B3556723 : Blo 984595 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B2999699 : Blo 984595 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B3163735 : Blo 984595 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B3327803 : Blo 984595 3327803 := bstep (se 1 (by rfl) ⟨2495852, by rfl⟩ : syracuseStep 3327803 = 4991705) B4991705
theorem B1001359 : Blo 984595 1001359 := bstep (se 1 (by rfl) ⟨751019, by rfl⟩ : syracuseStep 1001359 = 1502039) B1502039
theorem B22759541 : Blo 984595 22759541 := bstep (se 5 (by rfl) ⟨1066853, by rfl⟩ : syracuseStep 22759541 = 2133707) B2133707
theorem B5687533 : Blo 984595 5687533 := bstep (se 3 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 5687533 = 2132825) B2132825
theorem B2803997 : Blo 984595 2803997 := bstep (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) B1051499
theorem B3328289 : Blo 984595 3328289 := bstep (se 2 (by rfl) ⟨1248108, by rfl⟩ : syracuseStep 3328289 = 2496217) B2496217
theorem B9488825 : Blo 984595 9488825 := bstep (se 2 (by rfl) ⟨3558309, by rfl⟩ : syracuseStep 9488825 = 7116619) B7116619
theorem B3001033 : Blo 984595 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B3001121 : Blo 984595 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B11258675 : Blo 984595 11258675 := bstep (se 1 (by rfl) ⟨8444006, by rfl⟩ : syracuseStep 11258675 = 16888013) B16888013
theorem B3328883 : Blo 984595 3328883 := bstep (se 1 (by rfl) ⟨2496662, by rfl⟩ : syracuseStep 3328883 = 4993325) B4993325
theorem B8015021 : Blo 984595 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B8441273 : Blo 984595 8441273 := bstep (se 2 (by rfl) ⟨3165477, by rfl⟩ : syracuseStep 8441273 = 6330955) B6330955
theorem B2215439 : Blo 984595 2215439 := bstep (se 1 (by rfl) ⟨1661579, by rfl⟩ : syracuseStep 2215439 = 3323159) B3323159
theorem B2215457 : Blo 984595 2215457 := bstep (se 2 (by rfl) ⟨830796, by rfl⟩ : syracuseStep 2215457 = 1661593) B1661593
theorem B25611875 : Blo 984595 25611875 := bstep (se 1 (by rfl) ⟨19208906, by rfl⟩ : syracuseStep 25611875 = 38417813) B38417813
theorem B5623415 : Blo 984595 5623415 := bstep (se 1 (by rfl) ⟨4217561, by rfl⟩ : syracuseStep 5623415 = 8435123) B8435123
theorem B5623667 : Blo 984595 5623667 := bstep (se 1 (by rfl) ⟨4217750, by rfl⟩ : syracuseStep 5623667 = 8435501) B8435501
theorem B2215799 : Blo 984595 2215799 := bstep (se 1 (by rfl) ⟨1661849, by rfl⟩ : syracuseStep 2215799 = 3323699) B3323699
theorem B2215979 : Blo 984595 2215979 := bstep (se 1 (by rfl) ⟨1661984, by rfl⟩ : syracuseStep 2215979 = 3323969) B3323969
theorem B7098455 : Blo 984595 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B5329097 : Blo 984595 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B6410477 : Blo 984595 6410477 := bstep (se 3 (by rfl) ⟨1201964, by rfl⟩ : syracuseStep 6410477 = 2403929) B2403929
theorem B2806103 : Blo 984595 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B5001587 : Blo 984595 5001587 := bstep (se 1 (by rfl) ⟨3751190, by rfl⟩ : syracuseStep 5001587 = 7502381) B7502381
theorem B2216339 : Blo 984595 2216339 := bstep (se 1 (by rfl) ⟨1662254, by rfl⟩ : syracuseStep 2216339 = 3324509) B3324509
theorem B2216393 : Blo 984595 2216393 := bstep (se 2 (by rfl) ⟨831147, by rfl⟩ : syracuseStep 2216393 = 1662295) B1662295
theorem B6312401 : Blo 984595 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B6411097 : Blo 984595 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B5002073 : Blo 984595 5002073 := bstep (se 2 (by rfl) ⟨1875777, by rfl⟩ : syracuseStep 5002073 = 3751555) B3751555
theorem B11228057 : Blo 984595 11228057 := bstep (se 2 (by rfl) ⟨4210521, by rfl⟩ : syracuseStep 11228057 = 8421043) B8421043
theorem B4740049 : Blo 984595 4740049 := bstep (se 2 (by rfl) ⟨1777518, by rfl⟩ : syracuseStep 4740049 = 3555037) B3555037
theorem B2217095 : Blo 984595 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B2806969 : Blo 984595 2806969 := bstep (se 2 (by rfl) ⟨1052613, by rfl⟩ : syracuseStep 2806969 = 2105227) B2105227
theorem B1332409 : Blo 984595 1332409 := bstep (se 2 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 1332409 = 999307) B999307
theorem B5625125 : Blo 984595 5625125 := bstep (se 4 (by rfl) ⟨527355, by rfl⟩ : syracuseStep 5625125 = 1054711) B1054711
theorem B2217275 : Blo 984595 2217275 := bstep (se 1 (by rfl) ⟨1662956, by rfl⟩ : syracuseStep 2217275 = 3325913) B3325913
theorem B3331475 : Blo 984595 3331475 := bstep (se 1 (by rfl) ⟨2498606, by rfl⟩ : syracuseStep 3331475 = 4997213) B4997213
theorem B2217401 : Blo 984595 2217401 := bstep (se 2 (by rfl) ⟨831525, by rfl⟩ : syracuseStep 2217401 = 1663051) B1663051
theorem B2807311 : Blo 984595 2807311 := bstep (se 1 (by rfl) ⟨2105483, by rfl⟩ : syracuseStep 2807311 = 4210967) B4210967
theorem B20239901 : Blo 984595 20239901 := bstep (se 3 (by rfl) ⟨3794981, by rfl⟩ : syracuseStep 20239901 = 7589963) B7589963
theorem B1332793 : Blo 984595 1332793 := bstep (se 2 (by rfl) ⟨499797, by rfl⟩ : syracuseStep 1332793 = 999595) B999595
theorem B2217743 : Blo 984595 2217743 := bstep (se 1 (by rfl) ⟨1663307, by rfl⟩ : syracuseStep 2217743 = 3326615) B3326615
theorem B2217761 : Blo 984595 2217761 := bstep (se 2 (by rfl) ⟨831660, by rfl⟩ : syracuseStep 2217761 = 1663321) B1663321
theorem B2807585 : Blo 984595 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B4741067 : Blo 984595 4741067 := bstep (se 1 (by rfl) ⟨3555800, by rfl⟩ : syracuseStep 4741067 = 7111601) B7111601
theorem B10115117 : Blo 984595 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B2218103 : Blo 984595 2218103 := bstep (se 1 (by rfl) ⟨1663577, by rfl⟩ : syracuseStep 2218103 = 3327155) B3327155
theorem B1923257 : Blo 984595 1923257 := bstep (se 2 (by rfl) ⟨721221, by rfl⟩ : syracuseStep 1923257 = 1442443) B1442443
theorem B5626057 : Blo 984595 5626057 := bstep (se 2 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 5626057 = 4219543) B4219543
theorem B2218283 : Blo 984595 2218283 := bstep (se 1 (by rfl) ⟨1663712, by rfl⟩ : syracuseStep 2218283 = 3327425) B3327425
theorem B1497403 : Blo 984595 1497403 := bstep (se 1 (by rfl) ⟨1123052, by rfl⟩ : syracuseStep 1497403 = 2246105) B2246105
theorem B2808199 : Blo 984595 2808199 := bstep (se 1 (by rfl) ⟨2106149, by rfl⟩ : syracuseStep 2808199 = 4212299) B4212299
theorem B1333675 : Blo 984595 1333675 := bstep (se 1 (by rfl) ⟨1000256, by rfl⟩ : syracuseStep 1333675 = 2000513) B2000513
theorem B1497545 : Blo 984595 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B2218643 : Blo 984595 2218643 := bstep (se 1 (by rfl) ⟨1663982, by rfl⟩ : syracuseStep 2218643 = 3327965) B3327965
theorem B3005075 : Blo 984595 3005075 := bstep (se 1 (by rfl) ⟨2253806, by rfl⟩ : syracuseStep 3005075 = 4507613) B4507613
theorem B1333945 : Blo 984595 1333945 := bstep (se 2 (by rfl) ⟨500229, by rfl⟩ : syracuseStep 1333945 = 1000459) B1000459
theorem B2218697 : Blo 984595 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B2808587 : Blo 984595 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B4217615 : Blo 984595 4217615 := bstep (se 1 (by rfl) ⟨3163211, by rfl⟩ : syracuseStep 4217615 = 6326423) B6326423
theorem B3332879 : Blo 984595 3332879 := bstep (se 1 (by rfl) ⟨2499659, by rfl⟩ : syracuseStep 3332879 = 4999319) B4999319
theorem B1661755 : Blo 984595 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B5004179 : Blo 984595 5004179 := bstep (se 1 (by rfl) ⟨3753134, by rfl⟩ : syracuseStep 5004179 = 7506269) B7506269
theorem B5331865 : Blo 984595 5331865 := bstep (se 2 (by rfl) ⟨1999449, by rfl⟩ : syracuseStep 5331865 = 3998899) B3998899
theorem B1661897 : Blo 984595 1661897 := bstep (se 2 (by rfl) ⟨623211, by rfl⟩ : syracuseStep 1661897 = 1246423) B1246423
theorem B11983895 : Blo 984595 11983895 := bstep (se 1 (by rfl) ⟨8987921, by rfl⟩ : syracuseStep 11983895 = 17975843) B17975843
theorem B3333149 : Blo 984595 3333149 := bstep (se 3 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 3333149 = 1249931) B1249931
theorem B5397623 : Blo 984595 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B2219399 : Blo 984595 2219399 := bstep (se 1 (by rfl) ⟨1664549, by rfl⟩ : syracuseStep 2219399 = 3329099) B3329099
theorem B2219579 : Blo 984595 2219579 := bstep (se 1 (by rfl) ⟨1664684, by rfl⟩ : syracuseStep 2219579 = 3329369) B3329369
theorem B1662599 : Blo 984595 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B2219705 : Blo 984595 2219705 := bstep (se 2 (by rfl) ⟨832389, by rfl⟩ : syracuseStep 2219705 = 1664779) B1664779
theorem B1335047 : Blo 984595 1335047 := bstep (se 1 (by rfl) ⟨1001285, by rfl⟩ : syracuseStep 1335047 = 2002571) B2002571
theorem B2252603 : Blo 984595 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B7495577 : Blo 984595 7495577 := bstep (se 2 (by rfl) ⟨2810841, by rfl⟩ : syracuseStep 7495577 = 5621683) B5621683
theorem B9494435 : Blo 984595 9494435 := bstep (se 1 (by rfl) ⟨7120826, by rfl⟩ : syracuseStep 9494435 = 14241653) B14241653
theorem B2220047 : Blo 984595 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B2809885 : Blo 984595 2809885 := bstep (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) B1053707
theorem B2220065 : Blo 984595 2220065 := bstep (se 2 (by rfl) ⟨832524, by rfl⟩ : syracuseStep 2220065 = 1665049) B1665049
theorem B1663247 : Blo 984595 1663247 := bstep (se 1 (by rfl) ⟨1247435, by rfl⟩ : syracuseStep 1663247 = 2494871) B2494871
theorem B2810227 : Blo 984595 2810227 := bstep (se 1 (by rfl) ⟨2107670, by rfl⟩ : syracuseStep 2810227 = 4215341) B4215341
theorem B2220407 : Blo 984595 2220407 := bstep (se 1 (by rfl) ⟨1665305, by rfl⟩ : syracuseStep 2220407 = 3330611) B3330611
theorem B21356945 : Blo 984595 21356945 := bstep (se 2 (by rfl) ⟨8008854, by rfl⟩ : syracuseStep 21356945 = 16017709) B16017709
theorem B2843027 : Blo 984595 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B3334553 : Blo 984595 3334553 := bstep (se 2 (by rfl) ⟨1250457, by rfl⟩ : syracuseStep 3334553 = 2500915) B2500915
theorem B1335739 : Blo 984595 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B2220587 : Blo 984595 2220587 := bstep (se 1 (by rfl) ⟨1665440, by rfl⟩ : syracuseStep 2220587 = 3330881) B3330881
theorem B1663787 : Blo 984595 1663787 := bstep (se 1 (by rfl) ⟨1247840, by rfl⟩ : syracuseStep 1663787 = 2495681) B2495681
theorem B2220947 : Blo 984595 2220947 := bstep (se 1 (by rfl) ⟨1665710, by rfl⟩ : syracuseStep 2220947 = 3331421) B3331421
theorem B2221001 : Blo 984595 2221001 := bstep (se 2 (by rfl) ⟨832875, by rfl⟩ : syracuseStep 2221001 = 1665751) B1665751
theorem B3335255 : Blo 984595 3335255 := bstep (se 1 (by rfl) ⟨2501441, by rfl⟩ : syracuseStep 3335255 = 5002883) B5002883
theorem B1664185 : Blo 984595 1664185 := bstep (se 2 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 1664185 = 1248139) B1248139
theorem B20243843 : Blo 984595 20243843 := bstep (se 1 (by rfl) ⟨15182882, by rfl⟩ : syracuseStep 20243843 = 30365765) B30365765
theorem B3335741 : Blo 984595 3335741 := bstep (se 3 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 3335741 = 1250903) B1250903
theorem B2221703 : Blo 984595 2221703 := bstep (se 1 (by rfl) ⟨1666277, by rfl⟩ : syracuseStep 2221703 = 3332555) B3332555
theorem B3368719 : Blo 984595 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B7497521 : Blo 984595 7497521 := bstep (se 2 (by rfl) ⟨2811570, by rfl⟩ : syracuseStep 7497521 = 5623141) B5623141
theorem B2221883 : Blo 984595 2221883 := bstep (se 1 (by rfl) ⟨1666412, by rfl⟩ : syracuseStep 2221883 = 3332825) B3332825
theorem B1664887 : Blo 984595 1664887 := bstep (se 1 (by rfl) ⟨1248665, by rfl⟩ : syracuseStep 1664887 = 2497331) B2497331
theorem B2222009 : Blo 984595 2222009 := bstep (se 2 (by rfl) ⟨833253, by rfl⟩ : syracuseStep 2222009 = 1666507) B1666507
theorem B1665083 : Blo 984595 1665083 := bstep (se 1 (by rfl) ⟨1248812, by rfl⟩ : syracuseStep 1665083 = 2497625) B2497625
theorem B5400695 : Blo 984595 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B4221047 : Blo 984595 4221047 := bstep (se 1 (by rfl) ⟨3165785, by rfl⟩ : syracuseStep 4221047 = 6331571) B6331571
theorem B1108111 : Blo 984595 1108111 := bstep (se 1 (by rfl) ⟨831083, by rfl⟩ : syracuseStep 1108111 = 1662167) B1662167
theorem B2222351 : Blo 984595 2222351 := bstep (se 1 (by rfl) ⟨1666763, by rfl⟩ : syracuseStep 2222351 = 3333527) B3333527
theorem B2222369 : Blo 984595 2222369 := bstep (se 2 (by rfl) ⟨833388, by rfl⟩ : syracuseStep 2222369 = 1666777) B1666777
theorem B1665481 : Blo 984595 1665481 := bstep (se 2 (by rfl) ⟨624555, by rfl⟩ : syracuseStep 1665481 = 1249111) B1249111
theorem B2222711 : Blo 984595 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B1108615 : Blo 984595 1108615 := bstep (se 1 (by rfl) ⟨831461, by rfl⟩ : syracuseStep 1108615 = 1662923) B1662923
theorem B2222891 : Blo 984595 2222891 := bstep (se 1 (by rfl) ⟨1667168, by rfl⟩ : syracuseStep 2222891 = 3334337) B3334337
theorem B6744883 : Blo 984595 6744883 := bstep (se 1 (by rfl) ⟨5058662, by rfl⟩ : syracuseStep 6744883 = 10117325) B10117325
theorem B1108795 : Blo 984595 1108795 := bstep (se 1 (by rfl) ⟨831596, by rfl⟩ : syracuseStep 1108795 = 1663193) B1663193
theorem B1403849 : Blo 984595 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B2812961 : Blo 984595 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B1666183 : Blo 984595 1666183 := bstep (se 1 (by rfl) ⟨1249637, by rfl⟩ : syracuseStep 1666183 = 2499275) B2499275
theorem B2813075 : Blo 984595 2813075 := bstep (se 1 (by rfl) ⟨2109806, by rfl⟩ : syracuseStep 2813075 = 4219613) B4219613
theorem B2223251 : Blo 984595 2223251 := bstep (se 1 (by rfl) ⟨1667438, by rfl⟩ : syracuseStep 2223251 = 3334877) B3334877
theorem B2223305 : Blo 984595 2223305 := bstep (se 2 (by rfl) ⟨833739, by rfl⟩ : syracuseStep 2223305 = 1667479) B1667479
theorem B1109263 : Blo 984595 1109263 := bstep (se 1 (by rfl) ⟨831947, by rfl⟩ : syracuseStep 1109263 = 1663895) B1663895
theorem B5992193 : Blo 984595 5992193 := bstep (se 2 (by rfl) ⟨2247072, by rfl⟩ : syracuseStep 5992193 = 4494145) B4494145
theorem B1109767 : Blo 984595 1109767 := bstep (se 1 (by rfl) ⟨832325, by rfl⟩ : syracuseStep 1109767 = 1664651) B1664651
theorem B1666831 : Blo 984595 1666831 := bstep (se 1 (by rfl) ⟨1250123, by rfl⟩ : syracuseStep 1666831 = 2500247) B2500247
theorem B1404715 : Blo 984595 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B2224007 : Blo 984595 2224007 := bstep (se 1 (by rfl) ⟨1668005, by rfl⟩ : syracuseStep 2224007 = 3336011) B3336011
theorem B2813849 : Blo 984595 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1109947 : Blo 984595 1109947 := bstep (se 1 (by rfl) ⟨832460, by rfl⟩ : syracuseStep 1109947 = 1664921) B1664921
theorem B2224187 : Blo 984595 2224187 := bstep (se 1 (by rfl) ⟨1668140, by rfl⟩ : syracuseStep 2224187 = 3336281) B3336281
theorem B2224313 : Blo 984595 2224313 := bstep (se 2 (by rfl) ⟨834117, by rfl⟩ : syracuseStep 2224313 = 1668235) B1668235
theorem B46723313 : Blo 984595 46723313 := bstep (se 2 (by rfl) ⟨17521242, by rfl⟩ : syracuseStep 46723313 = 35042485) B35042485
theorem B1667371 : Blo 984595 1667371 := bstep (se 1 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 1667371 = 2501057) B2501057
theorem B1110415 : Blo 984595 1110415 := bstep (se 1 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 1110415 = 1665623) B1665623
theorem B1667513 : Blo 984595 1667513 := bstep (se 2 (by rfl) ⟨625317, by rfl⟩ : syracuseStep 1667513 = 1250635) B1250635
theorem B1405831 : Blo 984595 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B1110919 : Blo 984595 1110919 := bstep (se 1 (by rfl) ⟨833189, by rfl⟩ : syracuseStep 1110919 = 1666379) B1666379
theorem B20771851 : Blo 984595 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B1111099 : Blo 984595 1111099 := bstep (se 1 (by rfl) ⟨833324, by rfl⟩ : syracuseStep 1111099 = 1666649) B1666649
theorem B1668215 : Blo 984595 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B9499781 : Blo 984595 9499781 := bstep (se 4 (by rfl) ⟨890604, by rfl⟩ : syracuseStep 9499781 = 1781209) B1781209
theorem B22771003 : Blo 984595 22771003 := bstep (se 1 (by rfl) ⟨17078252, by rfl⟩ : syracuseStep 22771003 = 34156505) B34156505
theorem B1111567 : Blo 984595 1111567 := bstep (se 1 (by rfl) ⟨833675, by rfl⟩ : syracuseStep 1111567 = 1667351) B1667351
theorem B1406651 : Blo 984595 1406651 := bstep (se 1 (by rfl) ⟨1054988, by rfl⟩ : syracuseStep 1406651 = 2109977) B2109977
theorem B1112071 : Blo 984595 1112071 := bstep (se 1 (by rfl) ⟨834053, by rfl⟩ : syracuseStep 1112071 = 1668107) B1668107
theorem B14219509 : Blo 984595 14219509 := bstep (se 5 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 14219509 = 1333079) B1333079
theorem B1407289 : Blo 984595 1407289 := bstep (se 2 (by rfl) ⟨527733, by rfl⟩ : syracuseStep 1407289 = 1055467) B1055467
theorem B1407403 : Blo 984595 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B9009893 : Blo 984595 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B7109869 : Blo 984595 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B1900217 : Blo 984595 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1998607 : Blo 984595 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B3997649 : Blo 984595 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B1802569 : Blo 984595 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B1901063 : Blo 984595 1901063 := bstep (se 1 (by rfl) ⟨1425797, by rfl⟩ : syracuseStep 1901063 = 2851595) B2851595
theorem B1999799 : Blo 984595 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B31163545 : Blo 984595 31163545 := bstep (se 2 (by rfl) ⟨11686329, by rfl⟩ : syracuseStep 31163545 = 23372659) B23372659
theorem B15173027 : Blo 984595 15173027 := bstep (se 1 (by rfl) ⟨11379770, by rfl⟩ : syracuseStep 15173027 = 22759541) B22759541
theorem B79136185 : Blo 984595 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B1869331 : Blo 984595 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B984615 : Blo 984595 984615 := bstep (se 1 (by rfl) ⟨738461, by rfl⟩ : syracuseStep 984615 = 1476923) B1476923
theorem B984655 : Blo 984595 984655 := bstep (se 1 (by rfl) ⟨738491, by rfl⟩ : syracuseStep 984655 = 1476983) B1476983
theorem B984671 : Blo 984595 984671 := bstep (se 1 (by rfl) ⟨738503, by rfl⟩ : syracuseStep 984671 = 1477007) B1477007
theorem B984699 : Blo 984595 984699 := bstep (se 1 (by rfl) ⟨738524, by rfl⟩ : syracuseStep 984699 = 1477049) B1477049
theorem B1246843 : Blo 984595 1246843 := bstep (se 1 (by rfl) ⟨935132, by rfl⟩ : syracuseStep 1246843 = 1870265) B1870265
theorem B6325883 : Blo 984595 6325883 := bstep (se 1 (by rfl) ⟨4744412, by rfl⟩ : syracuseStep 6325883 = 9488825) B9488825
theorem B984751 : Blo 984595 984751 := bstep (se 1 (by rfl) ⟨738563, by rfl⟩ : syracuseStep 984751 = 1477127) B1477127
theorem B984775 : Blo 984595 984775 := bstep (se 1 (by rfl) ⟨738581, by rfl⟩ : syracuseStep 984775 = 1477163) B1477163
theorem B984795 : Blo 984595 984795 := bstep (se 1 (by rfl) ⟨738596, by rfl⟩ : syracuseStep 984795 = 1477193) B1477193
theorem B6162169 : Blo 984595 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B984871 : Blo 984595 984871 := bstep (se 1 (by rfl) ⟨738653, by rfl⟩ : syracuseStep 984871 = 1477307) B1477307
theorem B984911 : Blo 984595 984911 := bstep (se 1 (by rfl) ⟨738683, by rfl⟩ : syracuseStep 984911 = 1477367) B1477367
theorem B984927 : Blo 984595 984927 := bstep (se 1 (by rfl) ⟨738695, by rfl⟩ : syracuseStep 984927 = 1477391) B1477391
theorem B1247071 : Blo 984595 1247071 := bstep (se 1 (by rfl) ⟨935303, by rfl⟩ : syracuseStep 1247071 = 1870607) B1870607
theorem B2000747 : Blo 984595 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B7505783 : Blo 984595 7505783 := bstep (se 1 (by rfl) ⟨5629337, by rfl⟩ : syracuseStep 7505783 = 11258675) B11258675
theorem B984955 : Blo 984595 984955 := bstep (se 1 (by rfl) ⟨738716, by rfl⟩ : syracuseStep 984955 = 1477433) B1477433
theorem B985007 : Blo 984595 985007 := bstep (se 1 (by rfl) ⟨738755, by rfl⟩ : syracuseStep 985007 = 1477511) B1477511
theorem B985031 : Blo 984595 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B985051 : Blo 984595 985051 := bstep (se 1 (by rfl) ⟨738788, by rfl⟩ : syracuseStep 985051 = 1477577) B1477577
theorem B985127 : Blo 984595 985127 := bstep (se 1 (by rfl) ⟨738845, by rfl⟩ : syracuseStep 985127 = 1477691) B1477691
theorem B985167 : Blo 984595 985167 := bstep (se 1 (by rfl) ⟨738875, by rfl⟩ : syracuseStep 985167 = 1477751) B1477751
theorem B985183 : Blo 984595 985183 := bstep (se 1 (by rfl) ⟨738887, by rfl⟩ : syracuseStep 985183 = 1477775) B1477775
theorem B27330659 : Blo 984595 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B5343347 : Blo 984595 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B985211 : Blo 984595 985211 := bstep (se 1 (by rfl) ⟨738908, by rfl⟩ : syracuseStep 985211 = 1477817) B1477817
theorem B985263 : Blo 984595 985263 := bstep (se 1 (by rfl) ⟨738947, by rfl⟩ : syracuseStep 985263 = 1477895) B1477895
theorem B985287 : Blo 984595 985287 := bstep (se 1 (by rfl) ⟨738965, by rfl⟩ : syracuseStep 985287 = 1477931) B1477931
theorem B985307 : Blo 984595 985307 := bstep (se 1 (by rfl) ⟨738980, by rfl⟩ : syracuseStep 985307 = 1477961) B1477961
theorem B985383 : Blo 984595 985383 := bstep (se 1 (by rfl) ⟨739037, by rfl⟩ : syracuseStep 985383 = 1478075) B1478075
theorem B985423 : Blo 984595 985423 := bstep (se 1 (by rfl) ⟨739067, by rfl⟩ : syracuseStep 985423 = 1478135) B1478135
theorem B1476959 : Blo 984595 1476959 := bstep (se 1 (by rfl) ⟨1107719, by rfl⟩ : syracuseStep 1476959 = 2215439) B2215439
theorem B985439 : Blo 984595 985439 := bstep (se 1 (by rfl) ⟨739079, by rfl⟩ : syracuseStep 985439 = 1478159) B1478159
theorem B4491625 : Blo 984595 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B1476971 : Blo 984595 1476971 := bstep (se 1 (by rfl) ⟨1107728, by rfl⟩ : syracuseStep 1476971 = 2215457) B2215457
theorem B985467 : Blo 984595 985467 := bstep (se 1 (by rfl) ⟨739100, by rfl⟩ : syracuseStep 985467 = 1478201) B1478201
theorem B7997825 : Blo 984595 7997825 := bstep (se 2 (by rfl) ⟨2999184, by rfl⟩ : syracuseStep 7997825 = 5998369) B5998369
theorem B2492815 : Blo 984595 2492815 := bstep (se 1 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 2492815 = 3739223) B3739223
theorem B17074583 : Blo 984595 17074583 := bstep (se 1 (by rfl) ⟨12805937, by rfl⟩ : syracuseStep 17074583 = 25611875) B25611875
theorem B985519 : Blo 984595 985519 := bstep (se 1 (by rfl) ⟨739139, by rfl⟩ : syracuseStep 985519 = 1478279) B1478279
theorem B1247663 : Blo 984595 1247663 := bstep (se 1 (by rfl) ⟨935747, by rfl⟩ : syracuseStep 1247663 = 1871495) B1871495
theorem B985543 : Blo 984595 985543 := bstep (se 1 (by rfl) ⟨739157, by rfl⟩ : syracuseStep 985543 = 1478315) B1478315
theorem B985563 : Blo 984595 985563 := bstep (se 1 (by rfl) ⟨739172, by rfl⟩ : syracuseStep 985563 = 1478345) B1478345
theorem B985639 : Blo 984595 985639 := bstep (se 1 (by rfl) ⟨739229, by rfl⟩ : syracuseStep 985639 = 1478459) B1478459
theorem B1477199 : Blo 984595 1477199 := bstep (se 1 (by rfl) ⟨1107899, by rfl⟩ : syracuseStep 1477199 = 2215799) B2215799
theorem B985679 : Blo 984595 985679 := bstep (se 1 (by rfl) ⟨739259, by rfl⟩ : syracuseStep 985679 = 1478519) B1478519
theorem B985695 : Blo 984595 985695 := bstep (se 1 (by rfl) ⟨739271, by rfl⟩ : syracuseStep 985695 = 1478543) B1478543
theorem B985723 : Blo 984595 985723 := bstep (se 1 (by rfl) ⟨739292, by rfl⟩ : syracuseStep 985723 = 1478585) B1478585
theorem B985775 : Blo 984595 985775 := bstep (se 1 (by rfl) ⟨739331, by rfl⟩ : syracuseStep 985775 = 1478663) B1478663
theorem B1477319 : Blo 984595 1477319 := bstep (se 1 (by rfl) ⟨1107989, by rfl⟩ : syracuseStep 1477319 = 2215979) B2215979
theorem B985799 : Blo 984595 985799 := bstep (se 1 (by rfl) ⟨739349, by rfl⟩ : syracuseStep 985799 = 1478699) B1478699
theorem B2493139 : Blo 984595 2493139 := bstep (se 1 (by rfl) ⟨1869854, by rfl⟩ : syracuseStep 2493139 = 3739709) B3739709
theorem B985819 : Blo 984595 985819 := bstep (se 1 (by rfl) ⟨739364, by rfl⟩ : syracuseStep 985819 = 1478729) B1478729
theorem B985895 : Blo 984595 985895 := bstep (se 1 (by rfl) ⟨739421, by rfl⟩ : syracuseStep 985895 = 1478843) B1478843
theorem B985935 : Blo 984595 985935 := bstep (se 1 (by rfl) ⟨739451, by rfl⟩ : syracuseStep 985935 = 1478903) B1478903
theorem B985951 : Blo 984595 985951 := bstep (se 1 (by rfl) ⟨739463, by rfl⟩ : syracuseStep 985951 = 1478927) B1478927
theorem B1477481 : Blo 984595 1477481 := bstep (se 2 (by rfl) ⟨554055, by rfl⟩ : syracuseStep 1477481 = 1108111) B1108111
theorem B985979 : Blo 984595 985979 := bstep (se 1 (by rfl) ⟨739484, by rfl⟩ : syracuseStep 985979 = 1478969) B1478969
theorem B986031 : Blo 984595 986031 := bstep (se 1 (by rfl) ⟨739523, by rfl⟩ : syracuseStep 986031 = 1479047) B1479047
theorem B1477559 : Blo 984595 1477559 := bstep (se 1 (by rfl) ⟨1108169, by rfl⟩ : syracuseStep 1477559 = 2216339) B2216339
theorem B986055 : Blo 984595 986055 := bstep (se 1 (by rfl) ⟨739541, by rfl⟩ : syracuseStep 986055 = 1479083) B1479083
theorem B1477595 : Blo 984595 1477595 := bstep (se 1 (by rfl) ⟨1108196, by rfl⟩ : syracuseStep 1477595 = 2216393) B2216393
theorem B986075 : Blo 984595 986075 := bstep (se 1 (by rfl) ⟨739556, by rfl⟩ : syracuseStep 986075 = 1479113) B1479113
theorem B986151 : Blo 984595 986151 := bstep (se 1 (by rfl) ⟨739613, by rfl⟩ : syracuseStep 986151 = 1479227) B1479227
theorem B986191 : Blo 984595 986191 := bstep (se 1 (by rfl) ⟨739643, by rfl⟩ : syracuseStep 986191 = 1479287) B1479287
theorem B986207 : Blo 984595 986207 := bstep (se 1 (by rfl) ⟨739655, by rfl⟩ : syracuseStep 986207 = 1479311) B1479311
theorem B986235 : Blo 984595 986235 := bstep (se 1 (by rfl) ⟨739676, by rfl⟩ : syracuseStep 986235 = 1479353) B1479353
theorem B986287 : Blo 984595 986287 := bstep (se 1 (by rfl) ⟨739715, by rfl⟩ : syracuseStep 986287 = 1479431) B1479431
theorem B986311 : Blo 984595 986311 := bstep (se 1 (by rfl) ⟨739733, by rfl⟩ : syracuseStep 986311 = 1479467) B1479467
theorem B986331 : Blo 984595 986331 := bstep (se 1 (by rfl) ⟨739748, by rfl⟩ : syracuseStep 986331 = 1479497) B1479497
theorem B986407 : Blo 984595 986407 := bstep (se 1 (by rfl) ⟨739805, by rfl⟩ : syracuseStep 986407 = 1479611) B1479611
theorem B986447 : Blo 984595 986447 := bstep (se 1 (by rfl) ⟨739835, by rfl⟩ : syracuseStep 986447 = 1479671) B1479671
theorem B986463 : Blo 984595 986463 := bstep (se 1 (by rfl) ⟨739847, by rfl⟩ : syracuseStep 986463 = 1479695) B1479695
theorem B986491 : Blo 984595 986491 := bstep (se 1 (by rfl) ⟨739868, by rfl⟩ : syracuseStep 986491 = 1479737) B1479737
theorem B1478063 : Blo 984595 1478063 := bstep (se 1 (by rfl) ⟨1108547, by rfl⟩ : syracuseStep 1478063 = 2217095) B2217095
theorem B986543 : Blo 984595 986543 := bstep (se 1 (by rfl) ⟨739907, by rfl⟩ : syracuseStep 986543 = 1479815) B1479815
theorem B986567 : Blo 984595 986567 := bstep (se 1 (by rfl) ⟨739925, by rfl⟩ : syracuseStep 986567 = 1479851) B1479851
theorem B986587 : Blo 984595 986587 := bstep (se 1 (by rfl) ⟨739940, by rfl⟩ : syracuseStep 986587 = 1479881) B1479881
theorem B1478153 : Blo 984595 1478153 := bstep (se 2 (by rfl) ⟨554307, by rfl⟩ : syracuseStep 1478153 = 1108615) B1108615
theorem B1478183 : Blo 984595 1478183 := bstep (se 1 (by rfl) ⟨1108637, by rfl⟩ : syracuseStep 1478183 = 2217275) B2217275
theorem B986663 : Blo 984595 986663 := bstep (se 1 (by rfl) ⟨739997, by rfl⟩ : syracuseStep 986663 = 1479995) B1479995
theorem B986703 : Blo 984595 986703 := bstep (se 1 (by rfl) ⟨740027, by rfl⟩ : syracuseStep 986703 = 1480055) B1480055
theorem B986719 : Blo 984595 986719 := bstep (se 1 (by rfl) ⟨740039, by rfl⟩ : syracuseStep 986719 = 1480079) B1480079
theorem B1478267 : Blo 984595 1478267 := bstep (se 1 (by rfl) ⟨1108700, by rfl⟩ : syracuseStep 1478267 = 2217401) B2217401
theorem B986747 : Blo 984595 986747 := bstep (se 1 (by rfl) ⟨740060, by rfl⟩ : syracuseStep 986747 = 1480121) B1480121
theorem B2494091 : Blo 984595 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B986799 : Blo 984595 986799 := bstep (se 1 (by rfl) ⟨740099, by rfl⟩ : syracuseStep 986799 = 1480199) B1480199
theorem B5705405 : Blo 984595 5705405 := bstep (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) B2139527
theorem B986823 : Blo 984595 986823 := bstep (se 1 (by rfl) ⟨740117, by rfl⟩ : syracuseStep 986823 = 1480235) B1480235
theorem B986843 : Blo 984595 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B1478393 : Blo 984595 1478393 := bstep (se 2 (by rfl) ⟨554397, by rfl⟩ : syracuseStep 1478393 = 1108795) B1108795
theorem B986919 : Blo 984595 986919 := bstep (se 1 (by rfl) ⟨740189, by rfl⟩ : syracuseStep 986919 = 1480379) B1480379
theorem B986959 : Blo 984595 986959 := bstep (se 1 (by rfl) ⟨740219, by rfl⟩ : syracuseStep 986959 = 1480439) B1480439
theorem B1478495 : Blo 984595 1478495 := bstep (se 1 (by rfl) ⟨1108871, by rfl⟩ : syracuseStep 1478495 = 2217743) B2217743
theorem B986975 : Blo 984595 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B1478507 : Blo 984595 1478507 := bstep (se 1 (by rfl) ⟨1108880, by rfl⟩ : syracuseStep 1478507 = 2217761) B2217761
theorem B1871723 : Blo 984595 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B987003 : Blo 984595 987003 := bstep (se 1 (by rfl) ⟨740252, by rfl⟩ : syracuseStep 987003 = 1480505) B1480505
theorem B987055 : Blo 984595 987055 := bstep (se 1 (by rfl) ⟨740291, by rfl⟩ : syracuseStep 987055 = 1480583) B1480583
theorem B987079 : Blo 984595 987079 := bstep (se 1 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 987079 = 1480619) B1480619
theorem B987099 : Blo 984595 987099 := bstep (se 1 (by rfl) ⟨740324, by rfl⟩ : syracuseStep 987099 = 1480649) B1480649
theorem B987175 : Blo 984595 987175 := bstep (se 1 (by rfl) ⟨740381, by rfl⟩ : syracuseStep 987175 = 1480763) B1480763
theorem B1478735 : Blo 984595 1478735 := bstep (se 1 (by rfl) ⟨1109051, by rfl⟩ : syracuseStep 1478735 = 2218103) B2218103
theorem B987215 : Blo 984595 987215 := bstep (se 1 (by rfl) ⟨740411, by rfl⟩ : syracuseStep 987215 = 1480823) B1480823
theorem B987231 : Blo 984595 987231 := bstep (se 1 (by rfl) ⟨740423, by rfl⟩ : syracuseStep 987231 = 1480847) B1480847
theorem B1282171 : Blo 984595 1282171 := bstep (se 1 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 1282171 = 1923257) B1923257
theorem B987259 : Blo 984595 987259 := bstep (se 1 (by rfl) ⟨740444, by rfl⟩ : syracuseStep 987259 = 1480889) B1480889
theorem B987311 : Blo 984595 987311 := bstep (se 1 (by rfl) ⟨740483, by rfl⟩ : syracuseStep 987311 = 1480967) B1480967
theorem B1478855 : Blo 984595 1478855 := bstep (se 1 (by rfl) ⟨1109141, by rfl⟩ : syracuseStep 1478855 = 2218283) B2218283
theorem B987335 : Blo 984595 987335 := bstep (se 1 (by rfl) ⟨740501, by rfl⟩ : syracuseStep 987335 = 1481003) B1481003
theorem B987355 : Blo 984595 987355 := bstep (se 1 (by rfl) ⟨740516, by rfl⟩ : syracuseStep 987355 = 1481033) B1481033
theorem B987431 : Blo 984595 987431 := bstep (se 1 (by rfl) ⟨740573, by rfl⟩ : syracuseStep 987431 = 1481147) B1481147
theorem B987471 : Blo 984595 987471 := bstep (se 1 (by rfl) ⟨740603, by rfl⟩ : syracuseStep 987471 = 1481207) B1481207
theorem B987487 : Blo 984595 987487 := bstep (se 1 (by rfl) ⟨740615, by rfl⟩ : syracuseStep 987487 = 1481231) B1481231
theorem B1479017 : Blo 984595 1479017 := bstep (se 2 (by rfl) ⟨554631, by rfl⟩ : syracuseStep 1479017 = 1109263) B1109263
theorem B987515 : Blo 984595 987515 := bstep (se 1 (by rfl) ⟨740636, by rfl⟩ : syracuseStep 987515 = 1481273) B1481273
theorem B987567 : Blo 984595 987567 := bstep (se 1 (by rfl) ⟨740675, by rfl⟩ : syracuseStep 987567 = 1481351) B1481351
theorem B1479095 : Blo 984595 1479095 := bstep (se 1 (by rfl) ⟨1109321, by rfl⟩ : syracuseStep 1479095 = 2218643) B2218643
theorem B2003383 : Blo 984595 2003383 := bstep (se 1 (by rfl) ⟨1502537, by rfl⟩ : syracuseStep 2003383 = 3005075) B3005075
theorem B987591 : Blo 984595 987591 := bstep (se 1 (by rfl) ⟨740693, by rfl⟩ : syracuseStep 987591 = 1481387) B1481387
theorem B1479131 : Blo 984595 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B987611 : Blo 984595 987611 := bstep (se 1 (by rfl) ⟨740708, by rfl⟩ : syracuseStep 987611 = 1481417) B1481417
theorem B1872391 : Blo 984595 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B987687 : Blo 984595 987687 := bstep (se 1 (by rfl) ⟨740765, by rfl⟩ : syracuseStep 987687 = 1481531) B1481531
theorem B1053263 : Blo 984595 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B987727 : Blo 984595 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B987743 : Blo 984595 987743 := bstep (se 1 (by rfl) ⟨740807, by rfl⟩ : syracuseStep 987743 = 1481615) B1481615
theorem B987771 : Blo 984595 987771 := bstep (se 1 (by rfl) ⟨740828, by rfl⟩ : syracuseStep 987771 = 1481657) B1481657
theorem B987823 : Blo 984595 987823 := bstep (se 1 (by rfl) ⟨740867, by rfl⟩ : syracuseStep 987823 = 1481735) B1481735
theorem B987847 : Blo 984595 987847 := bstep (se 1 (by rfl) ⟨740885, by rfl⟩ : syracuseStep 987847 = 1481771) B1481771
theorem B18977489 : Blo 984595 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B987867 : Blo 984595 987867 := bstep (se 1 (by rfl) ⟨740900, by rfl⟩ : syracuseStep 987867 = 1481801) B1481801
theorem B2495225 : Blo 984595 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B987943 : Blo 984595 987943 := bstep (se 1 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 987943 = 1481915) B1481915
theorem B987983 : Blo 984595 987983 := bstep (se 1 (by rfl) ⟨740987, by rfl⟩ : syracuseStep 987983 = 1481975) B1481975
theorem B987999 : Blo 984595 987999 := bstep (se 1 (by rfl) ⟨740999, by rfl⟩ : syracuseStep 987999 = 1481999) B1481999
theorem B988027 : Blo 984595 988027 := bstep (se 1 (by rfl) ⟨741020, by rfl⟩ : syracuseStep 988027 = 1482041) B1482041
theorem B2495407 : Blo 984595 2495407 := bstep (se 1 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 2495407 = 3743111) B3743111
theorem B1479599 : Blo 984595 1479599 := bstep (se 1 (by rfl) ⟨1109699, by rfl⟩ : syracuseStep 1479599 = 2219399) B2219399
theorem B988079 : Blo 984595 988079 := bstep (se 1 (by rfl) ⟨741059, by rfl⟩ : syracuseStep 988079 = 1482119) B1482119
theorem B988103 : Blo 984595 988103 := bstep (se 1 (by rfl) ⟨741077, by rfl⟩ : syracuseStep 988103 = 1482155) B1482155
theorem B988123 : Blo 984595 988123 := bstep (se 1 (by rfl) ⟨741092, by rfl⟩ : syracuseStep 988123 = 1482185) B1482185
theorem B19502045 : Blo 984595 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B1479689 : Blo 984595 1479689 := bstep (se 2 (by rfl) ⟨554883, by rfl⟩ : syracuseStep 1479689 = 1109767) B1109767
theorem B1479719 : Blo 984595 1479719 := bstep (se 1 (by rfl) ⟨1109789, by rfl⟩ : syracuseStep 1479719 = 2219579) B2219579
theorem B988199 : Blo 984595 988199 := bstep (se 1 (by rfl) ⟨741149, by rfl⟩ : syracuseStep 988199 = 1482299) B1482299
theorem B1872953 : Blo 984595 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B988239 : Blo 984595 988239 := bstep (se 1 (by rfl) ⟨741179, by rfl⟩ : syracuseStep 988239 = 1482359) B1482359
theorem B988255 : Blo 984595 988255 := bstep (se 1 (by rfl) ⟨741191, by rfl⟩ : syracuseStep 988255 = 1482383) B1482383
theorem B1479803 : Blo 984595 1479803 := bstep (se 1 (by rfl) ⟨1109852, by rfl⟩ : syracuseStep 1479803 = 2219705) B2219705
theorem B988283 : Blo 984595 988283 := bstep (se 1 (by rfl) ⟨741212, by rfl⟩ : syracuseStep 988283 = 1482425) B1482425
theorem B988335 : Blo 984595 988335 := bstep (se 1 (by rfl) ⟨741251, by rfl⟩ : syracuseStep 988335 = 1482503) B1482503
theorem B1053895 : Blo 984595 1053895 := bstep (se 1 (by rfl) ⟨790421, by rfl⟩ : syracuseStep 1053895 = 1580843) B1580843
theorem B988359 : Blo 984595 988359 := bstep (se 1 (by rfl) ⟨741269, by rfl⟩ : syracuseStep 988359 = 1482539) B1482539
theorem B988379 : Blo 984595 988379 := bstep (se 1 (by rfl) ⟨741284, by rfl⟩ : syracuseStep 988379 = 1482569) B1482569
theorem B1479929 : Blo 984595 1479929 := bstep (se 2 (by rfl) ⟨554973, by rfl⟩ : syracuseStep 1479929 = 1109947) B1109947
theorem B6329623 : Blo 984595 6329623 := bstep (se 1 (by rfl) ⟨4747217, by rfl⟩ : syracuseStep 6329623 = 9494435) B9494435
theorem B988455 : Blo 984595 988455 := bstep (se 1 (by rfl) ⟨741341, by rfl⟩ : syracuseStep 988455 = 1482683) B1482683
theorem B988495 : Blo 984595 988495 := bstep (se 1 (by rfl) ⟨741371, by rfl⟩ : syracuseStep 988495 = 1482743) B1482743
theorem B1480031 : Blo 984595 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B988511 : Blo 984595 988511 := bstep (se 1 (by rfl) ⟨741383, by rfl⟩ : syracuseStep 988511 = 1482767) B1482767
theorem B1480043 : Blo 984595 1480043 := bstep (se 1 (by rfl) ⟨1110032, by rfl⟩ : syracuseStep 1480043 = 2220065) B2220065
theorem B988539 : Blo 984595 988539 := bstep (se 1 (by rfl) ⟨741404, by rfl⟩ : syracuseStep 988539 = 1482809) B1482809
theorem B2495873 : Blo 984595 2495873 := bstep (se 2 (by rfl) ⟨935952, by rfl⟩ : syracuseStep 2495873 = 1871905) B1871905
theorem B988591 : Blo 984595 988591 := bstep (se 1 (by rfl) ⟨741443, by rfl⟩ : syracuseStep 988591 = 1482887) B1482887
theorem B1480271 : Blo 984595 1480271 := bstep (se 1 (by rfl) ⟨1110203, by rfl⟩ : syracuseStep 1480271 = 2220407) B2220407
theorem B1480391 : Blo 984595 1480391 := bstep (se 1 (by rfl) ⟨1110293, by rfl⟩ : syracuseStep 1480391 = 2220587) B2220587
theorem B10819271 : Blo 984595 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B2496329 : Blo 984595 2496329 := bstep (se 2 (by rfl) ⟨936123, by rfl⟩ : syracuseStep 2496329 = 1872247) B1872247
theorem B1480553 : Blo 984595 1480553 := bstep (se 2 (by rfl) ⟨555207, by rfl⟩ : syracuseStep 1480553 = 1110415) B1110415
theorem B3741623 : Blo 984595 3741623 := bstep (se 1 (by rfl) ⟨2806217, by rfl⟩ : syracuseStep 3741623 = 5612435) B5612435
theorem B1480631 : Blo 984595 1480631 := bstep (se 1 (by rfl) ⟨1110473, by rfl⟩ : syracuseStep 1480631 = 2220947) B2220947
theorem B1480667 : Blo 984595 1480667 := bstep (se 1 (by rfl) ⟨1110500, by rfl⟩ : syracuseStep 1480667 = 2221001) B2221001
theorem B2496683 : Blo 984595 2496683 := bstep (se 1 (by rfl) ⟨1872512, by rfl⟩ : syracuseStep 2496683 = 3745025) B3745025
theorem B1481135 : Blo 984595 1481135 := bstep (se 1 (by rfl) ⟨1110851, by rfl⟩ : syracuseStep 1481135 = 2221703) B2221703
theorem B1776055 : Blo 984595 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B1186267 : Blo 984595 1186267 := bstep (se 1 (by rfl) ⟨889700, by rfl⟩ : syracuseStep 1186267 = 1779401) B1779401
theorem B1874441 : Blo 984595 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B1481225 : Blo 984595 1481225 := bstep (se 2 (by rfl) ⟨555459, by rfl⟩ : syracuseStep 1481225 = 1110919) B1110919
theorem B1481255 : Blo 984595 1481255 := bstep (se 1 (by rfl) ⟨1110941, by rfl⟩ : syracuseStep 1481255 = 2221883) B2221883
theorem B1776251 : Blo 984595 1776251 := bstep (se 1 (by rfl) ⟨1332188, by rfl⟩ : syracuseStep 1776251 = 2664377) B2664377
theorem B1481339 : Blo 984595 1481339 := bstep (se 1 (by rfl) ⟨1111004, by rfl⟩ : syracuseStep 1481339 = 2222009) B2222009
theorem B27695801 : Blo 984595 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B12655349 : Blo 984595 12655349 := bstep (se 5 (by rfl) ⟨593219, by rfl⟩ : syracuseStep 12655349 = 1186439) B1186439
theorem B1481465 : Blo 984595 1481465 := bstep (se 2 (by rfl) ⟨555549, by rfl⟩ : syracuseStep 1481465 = 1111099) B1111099
theorem B1481567 : Blo 984595 1481567 := bstep (se 1 (by rfl) ⟨1111175, by rfl⟩ : syracuseStep 1481567 = 2222351) B2222351
theorem B1481579 : Blo 984595 1481579 := bstep (se 1 (by rfl) ⟨1111184, by rfl⟩ : syracuseStep 1481579 = 2222369) B2222369
theorem B3742625 : Blo 984595 3742625 := bstep (se 2 (by rfl) ⟨1403484, by rfl⟩ : syracuseStep 3742625 = 2806969) B2806969
theorem B1776545 : Blo 984595 1776545 := bstep (se 2 (by rfl) ⟨666204, by rfl⟩ : syracuseStep 1776545 = 1332409) B1332409
theorem B2497463 : Blo 984595 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B2104339 : Blo 984595 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B1481807 : Blo 984595 1481807 := bstep (se 1 (by rfl) ⟨1111355, by rfl⟩ : syracuseStep 1481807 = 2222711) B2222711
theorem B7609423 : Blo 984595 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B1481927 : Blo 984595 1481927 := bstep (se 1 (by rfl) ⟨1111445, by rfl⟩ : syracuseStep 1481927 = 2222891) B2222891
theorem B24026381 : Blo 984595 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B3743081 : Blo 984595 3743081 := bstep (se 2 (by rfl) ⟨1403655, by rfl⟩ : syracuseStep 3743081 = 2807311) B2807311
theorem B1482089 : Blo 984595 1482089 := bstep (se 2 (by rfl) ⟨555783, by rfl⟩ : syracuseStep 1482089 = 1111567) B1111567
theorem B1875307 : Blo 984595 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B4988303 : Blo 984595 4988303 := bstep (se 1 (by rfl) ⟨3741227, by rfl⟩ : syracuseStep 4988303 = 7482455) B7482455
theorem B1875383 : Blo 984595 1875383 := bstep (se 1 (by rfl) ⟨1406537, by rfl⟩ : syracuseStep 1875383 = 2813075) B2813075
theorem B1482167 : Blo 984595 1482167 := bstep (se 1 (by rfl) ⟨1111625, by rfl⟩ : syracuseStep 1482167 = 2223251) B2223251
theorem B1482203 : Blo 984595 1482203 := bstep (se 1 (by rfl) ⟨1111652, by rfl⟩ : syracuseStep 1482203 = 2223305) B2223305
theorem B3743597 : Blo 984595 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B2498465 : Blo 984595 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B1777583 : Blo 984595 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1482671 : Blo 984595 1482671 := bstep (se 1 (by rfl) ⟨1112003, by rfl⟩ : syracuseStep 1482671 = 2224007) B2224007
theorem B1875899 : Blo 984595 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B1482761 : Blo 984595 1482761 := bstep (se 2 (by rfl) ⟨556035, by rfl⟩ : syracuseStep 1482761 = 1112071) B1112071
theorem B46768141 : Blo 984595 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B1482791 : Blo 984595 1482791 := bstep (se 1 (by rfl) ⟨1112093, by rfl⟩ : syracuseStep 1482791 = 2224187) B2224187
theorem B1482875 : Blo 984595 1482875 := bstep (se 1 (by rfl) ⟨1112156, by rfl⟩ : syracuseStep 1482875 = 2224313) B2224313
theorem B15212875 : Blo 984595 15212875 := bstep (se 1 (by rfl) ⟨11409656, by rfl⟩ : syracuseStep 15212875 = 22819313) B22819313
theorem B2498921 : Blo 984595 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B1876385 : Blo 984595 1876385 := bstep (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) B1407289
theorem B3744265 : Blo 984595 3744265 := bstep (se 2 (by rfl) ⟨1404099, by rfl⟩ : syracuseStep 3744265 = 2808199) B2808199
theorem B1778233 : Blo 984595 1778233 := bstep (se 2 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 1778233 = 1333675) B1333675
theorem B1876537 : Blo 984595 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B6333187 : Blo 984595 6333187 := bstep (se 1 (by rfl) ⟨4749890, by rfl⟩ : syracuseStep 6333187 = 9499781) B9499781
theorem B1778593 : Blo 984595 1778593 := bstep (se 2 (by rfl) ⟨666972, by rfl⟩ : syracuseStep 1778593 = 1333945) B1333945
theorem B3154945 : Blo 984595 3154945 := bstep (se 2 (by rfl) ⟨1183104, by rfl⟩ : syracuseStep 3154945 = 2366209) B2366209
theorem B4006991 : Blo 984595 4006991 := bstep (se 1 (by rfl) ⟨3005243, by rfl⟩ : syracuseStep 4006991 = 6010487) B6010487
theorem B12002575 : Blo 984595 12002575 := bstep (se 1 (by rfl) ⟨9001931, by rfl⟩ : syracuseStep 12002575 = 18003863) B18003863
theorem B4990409 : Blo 984595 4990409 := bstep (se 2 (by rfl) ⟨1871403, by rfl⟩ : syracuseStep 4990409 = 3742807) B3742807
theorem B2500105 : Blo 984595 2500105 := bstep (se 2 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 2500105 = 1875079) B1875079
theorem B9479825 : Blo 984595 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B2107243 : Blo 984595 2107243 := bstep (se 1 (by rfl) ⟨1580432, by rfl⟩ : syracuseStep 2107243 = 3160865) B3160865
theorem B3155831 : Blo 984595 3155831 := bstep (se 1 (by rfl) ⟨2366873, by rfl⟩ : syracuseStep 3155831 = 4733747) B4733747
theorem B3745723 : Blo 984595 3745723 := bstep (se 1 (by rfl) ⟨2809292, by rfl⟩ : syracuseStep 3745723 = 5618585) B5618585
theorem B1583111 : Blo 984595 1583111 := bstep (se 1 (by rfl) ⟨1187333, by rfl⟩ : syracuseStep 1583111 = 2374667) B2374667
theorem B3156047 : Blo 984595 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B4991057 : Blo 984595 4991057 := bstep (se 2 (by rfl) ⟨1871646, by rfl⟩ : syracuseStep 4991057 = 3743293) B3743293
theorem B2664809 : Blo 984595 2664809 := bstep (se 2 (by rfl) ⟨999303, by rfl⟩ : syracuseStep 2664809 = 1998607) B1998607
theorem B2370073 : Blo 984595 2370073 := bstep (se 2 (by rfl) ⟨888777, by rfl⟩ : syracuseStep 2370073 = 1777555) B1777555
theorem B2665099 : Blo 984595 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B1780423 : Blo 984595 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B3746513 : Blo 984595 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B2501563 : Blo 984595 2501563 := bstep (se 1 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 2501563 = 3752345) B3752345
theorem B2108423 : Blo 984595 2108423 := bstep (se 1 (by rfl) ⟨1581317, by rfl⟩ : syracuseStep 2108423 = 3162635) B3162635
theorem B3746969 : Blo 984595 3746969 := bstep (se 2 (by rfl) ⟨1405113, by rfl⟩ : syracuseStep 3746969 = 2810227) B2810227
theorem B3157163 : Blo 984595 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B1780985 : Blo 984595 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B10792435 : Blo 984595 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B7482941 : Blo 984595 7482941 := bstep (se 3 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 7482941 = 2806103) B2806103
theorem B4206269 : Blo 984595 4206269 := bstep (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) B1577351
theorem B9613187 : Blo 984595 9613187 := bstep (se 1 (by rfl) ⟨7209890, by rfl⟩ : syracuseStep 9613187 = 14419781) B14419781
theorem B6008737 : Blo 984595 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B7483913 : Blo 984595 7483913 := bstep (se 2 (by rfl) ⟨2806467, by rfl⟩ : syracuseStep 7483913 = 5612935) B5612935
theorem B1684319 : Blo 984595 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B3748943 : Blo 984595 3748943 := bstep (se 1 (by rfl) ⟨2811707, by rfl⟩ : syracuseStep 3748943 = 5623415) B5623415
theorem B3323051 : Blo 984595 3323051 := bstep (se 1 (by rfl) ⟨2492288, by rfl⟩ : syracuseStep 3323051 = 4984577) B4984577
theorem B3749111 : Blo 984595 3749111 := bstep (se 1 (by rfl) ⟨2811833, by rfl⟩ : syracuseStep 3749111 = 5623667) B5623667
theorem B4732303 : Blo 984595 4732303 := bstep (se 1 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 4732303 = 7098455) B7098455
theorem B3552731 : Blo 984595 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B4273651 : Blo 984595 4273651 := bstep (se 1 (by rfl) ⟨3205238, by rfl⟩ : syracuseStep 4273651 = 6410477) B6410477
theorem B4208267 : Blo 984595 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B7583377 : Blo 984595 7583377 := bstep (se 2 (by rfl) ⟨2843766, by rfl⟩ : syracuseStep 7583377 = 5687533) B5687533
theorem B3159737 : Blo 984595 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B3323591 : Blo 984595 3323591 := bstep (se 1 (by rfl) ⟨2492693, by rfl⟩ : syracuseStep 3323591 = 4985387) B4985387
theorem B7485371 : Blo 984595 7485371 := bstep (se 1 (by rfl) ⟨5614028, by rfl⟩ : syracuseStep 7485371 = 11228057) B11228057
theorem B7125155 : Blo 984595 7125155 := bstep (se 1 (by rfl) ⟨5343866, by rfl⟩ : syracuseStep 7125155 = 10687733) B10687733
theorem B3750083 : Blo 984595 3750083 := bstep (se 1 (by rfl) ⟨2812562, by rfl⟩ : syracuseStep 3750083 = 5625125) B5625125
theorem B16005509 : Blo 984595 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B8993177 : Blo 984595 8993177 := bstep (se 2 (by rfl) ⟨3372441, by rfl⟩ : syracuseStep 8993177 = 6744883) B6744883
theorem B4995593 : Blo 984595 4995593 := bstep (se 2 (by rfl) ⟨1873347, by rfl⟩ : syracuseStep 4995593 = 3746695) B3746695
theorem B3324455 : Blo 984595 3324455 := bstep (se 1 (by rfl) ⟨2493341, by rfl⟩ : syracuseStep 3324455 = 4986683) B4986683
theorem B3160711 : Blo 984595 3160711 := bstep (se 1 (by rfl) ⟨2370533, by rfl⟩ : syracuseStep 3160711 = 4741067) B4741067
theorem B3324563 : Blo 984595 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B2407241 : Blo 984595 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B3324779 : Blo 984595 3324779 := bstep (se 1 (by rfl) ⟨2493584, by rfl⟩ : syracuseStep 3324779 = 4987169) B4987169
theorem B3324833 : Blo 984595 3324833 := bstep (se 2 (by rfl) ⟨1246812, by rfl⟩ : syracuseStep 3324833 = 2493625) B2493625
theorem B998363 : Blo 984595 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B5618767 : Blo 984595 5618767 := bstep (se 1 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 5618767 = 8428151) B8428151
theorem B3751069 : Blo 984595 3751069 := bstep (se 3 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 3751069 = 1406651) B1406651
theorem B3325427 : Blo 984595 3325427 := bstep (se 1 (by rfl) ⟨2494070, by rfl⟩ : syracuseStep 3325427 = 4988141) B4988141
theorem B9879329 : Blo 984595 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B10141625 : Blo 984595 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B4997051 : Blo 984595 4997051 := bstep (se 1 (by rfl) ⟨3747788, by rfl⟩ : syracuseStep 4997051 = 7495577) B7495577
theorem B3325967 : Blo 984595 3325967 := bstep (se 1 (by rfl) ⟨2494475, by rfl⟩ : syracuseStep 3325967 = 4988951) B4988951
theorem B14237963 : Blo 984595 14237963 := bstep (se 1 (by rfl) ⟨10678472, by rfl⟩ : syracuseStep 14237963 = 21356945) B21356945
theorem B3162493 : Blo 984595 3162493 := bstep (se 3 (by rfl) ⟨592967, by rfl⟩ : syracuseStep 3162493 = 1185935) B1185935
theorem B3293729 : Blo 984595 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B3326561 : Blo 984595 3326561 := bstep (se 2 (by rfl) ⟨1247460, by rfl⟩ : syracuseStep 3326561 = 2494921) B2494921
theorem B2999467 : Blo 984595 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B4998347 : Blo 984595 4998347 := bstep (se 1 (by rfl) ⟨3748760, by rfl⟩ : syracuseStep 4998347 = 7497521) B7497521
theorem B30361337 : Blo 984595 30361337 := bstep (se 2 (by rfl) ⟨11385501, by rfl⟩ : syracuseStep 30361337 = 22771003) B22771003
theorem B4212641 : Blo 984595 4212641 := bstep (se 2 (by rfl) ⟨1579740, by rfl⟩ : syracuseStep 4212641 = 3159481) B3159481
theorem B3328019 : Blo 984595 3328019 := bstep (se 1 (by rfl) ⟨2496014, by rfl⟩ : syracuseStep 3328019 = 4992029) B4992029
theorem B3328343 : Blo 984595 3328343 := bstep (se 1 (by rfl) ⟨2496257, by rfl⟩ : syracuseStep 3328343 = 4992515) B4992515
theorem B31148875 : Blo 984595 31148875 := bstep (se 1 (by rfl) ⟨23361656, by rfl⟩ : syracuseStep 31148875 = 46723313) B46723313
theorem B18959345 : Blo 984595 18959345 := bstep (se 2 (by rfl) ⟨7109754, by rfl⟩ : syracuseStep 18959345 = 14219509) B14219509
theorem B3329423 : Blo 984595 3329423 := bstep (se 1 (by rfl) ⟨2497067, by rfl⟩ : syracuseStep 3329423 = 4994135) B4994135
theorem B2215547 : Blo 984595 2215547 := bstep (se 1 (by rfl) ⟨1661660, by rfl⟩ : syracuseStep 2215547 = 3323321) B3323321
theorem B3329747 : Blo 984595 3329747 := bstep (se 1 (by rfl) ⟨2497310, by rfl⟩ : syracuseStep 3329747 = 4994621) B4994621
theorem B2215673 : Blo 984595 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B2215943 : Blo 984595 2215943 := bstep (se 1 (by rfl) ⟨1661957, by rfl⟩ : syracuseStep 2215943 = 3323915) B3323915
theorem B3002447 : Blo 984595 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B2216015 : Blo 984595 2216015 := bstep (se 1 (by rfl) ⟨1662011, by rfl⟩ : syracuseStep 2216015 = 3324023) B3324023
theorem B6082675 : Blo 984595 6082675 := bstep (se 1 (by rfl) ⟨4562006, by rfl⟩ : syracuseStep 6082675 = 9124013) B9124013
theorem B11260133 : Blo 984595 11260133 := bstep (se 4 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 11260133 = 2111275) B2111275
theorem B4215169 : Blo 984595 4215169 := bstep (se 2 (by rfl) ⟨1580688, by rfl⟩ : syracuseStep 4215169 = 3161377) B3161377
theorem B2216411 : Blo 984595 2216411 := bstep (se 1 (by rfl) ⟨1662308, by rfl⟩ : syracuseStep 2216411 = 3324617) B3324617
theorem B5067245 : Blo 984595 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B3560125 : Blo 984595 3560125 := bstep (se 3 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 3560125 = 1335047) B1335047
theorem B3330935 : Blo 984595 3330935 := bstep (se 1 (by rfl) ⟨2498201, by rfl⟩ : syracuseStep 3330935 = 4996403) B4996403
theorem B2216879 : Blo 984595 2216879 := bstep (se 1 (by rfl) ⟨1662659, by rfl⟩ : syracuseStep 2216879 = 3325319) B3325319
theorem B3331151 : Blo 984595 3331151 := bstep (se 1 (by rfl) ⟨2498363, by rfl⟩ : syracuseStep 3331151 = 4996727) B4996727
theorem B2217131 : Blo 984595 2217131 := bstep (se 1 (by rfl) ⟨1662848, by rfl⟩ : syracuseStep 2217131 = 3325697) B3325697
theorem B30365027 : Blo 984595 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B3331529 : Blo 984595 3331529 := bstep (se 2 (by rfl) ⟨1249323, by rfl⟩ : syracuseStep 3331529 = 2498647) B2498647
theorem B25286093 : Blo 984595 25286093 := bstep (se 3 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 25286093 = 9482285) B9482285
theorem B2217671 : Blo 984595 2217671 := bstep (se 1 (by rfl) ⟨1663253, by rfl⟩ : syracuseStep 2217671 = 3326507) B3326507
theorem B3331799 : Blo 984595 3331799 := bstep (se 1 (by rfl) ⟨2498849, by rfl⟩ : syracuseStep 3331799 = 4997699) B4997699
theorem B6313787 : Blo 984595 6313787 := bstep (se 1 (by rfl) ⟨4735340, by rfl⟩ : syracuseStep 6313787 = 9470681) B9470681
theorem B3332015 : Blo 984595 3332015 := bstep (se 1 (by rfl) ⟨2499011, by rfl⟩ : syracuseStep 3332015 = 4998023) B4998023
theorem B5003531 : Blo 984595 5003531 := bstep (se 1 (by rfl) ⟨3752648, by rfl⟩ : syracuseStep 5003531 = 7505297) B7505297
theorem B2218535 : Blo 984595 2218535 := bstep (se 1 (by rfl) ⟨1663901, by rfl⟩ : syracuseStep 2218535 = 3327803) B3327803
theorem B1661519 : Blo 984595 1661519 := bstep (se 1 (by rfl) ⟨1246139, by rfl⟩ : syracuseStep 1661519 = 2492279) B2492279
theorem B2218859 : Blo 984595 2218859 := bstep (se 1 (by rfl) ⟨1664144, by rfl⟩ : syracuseStep 2218859 = 3328289) B3328289
theorem B2218913 : Blo 984595 2218913 := bstep (se 2 (by rfl) ⟨832092, by rfl⟩ : syracuseStep 2218913 = 1664185) B1664185
theorem B4742297 : Blo 984595 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B2219255 : Blo 984595 2219255 := bstep (se 1 (by rfl) ⟨1664441, by rfl⟩ : syracuseStep 2219255 = 3328883) B3328883
theorem B1662383 : Blo 984595 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B48717233 : Blo 984595 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B4218313 : Blo 984595 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B5627515 : Blo 984595 5627515 := bstep (se 1 (by rfl) ⟨4220636, by rfl⟩ : syracuseStep 5627515 = 8441273) B8441273
theorem B1334983 : Blo 984595 1334983 := bstep (se 1 (by rfl) ⟨1001237, by rfl⟩ : syracuseStep 1334983 = 2002475) B2002475
theorem B2219849 : Blo 984595 2219849 := bstep (se 2 (by rfl) ⟨832443, by rfl⟩ : syracuseStep 2219849 = 1664887) B1664887
theorem B1662815 : Blo 984595 1662815 := bstep (se 1 (by rfl) ⟨1247111, by rfl⟩ : syracuseStep 1662815 = 2494223) B2494223
theorem B1335145 : Blo 984595 1335145 := bstep (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) B1001359
theorem B1335215 : Blo 984595 1335215 := bstep (se 1 (by rfl) ⟨1001411, by rfl⟩ : syracuseStep 1335215 = 2002823) B2002823
theorem B2252819 : Blo 984595 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B3334391 : Blo 984595 3334391 := bstep (se 1 (by rfl) ⟨2500793, by rfl⟩ : syracuseStep 3334391 = 5001587) B5001587
theorem B7987517 : Blo 984595 7987517 := bstep (se 3 (by rfl) ⟨1497659, by rfl⟩ : syracuseStep 7987517 = 2995319) B2995319
theorem B1663375 : Blo 984595 1663375 := bstep (se 1 (by rfl) ⟨1247531, by rfl⟩ : syracuseStep 1663375 = 2495063) B2495063
theorem B3334715 : Blo 984595 3334715 := bstep (se 1 (by rfl) ⟨2501036, by rfl⟩ : syracuseStep 3334715 = 5002073) B5002073
theorem B2220641 : Blo 984595 2220641 := bstep (se 2 (by rfl) ⟨832740, by rfl⟩ : syracuseStep 2220641 = 1665481) B1665481
theorem B3334985 : Blo 984595 3334985 := bstep (se 2 (by rfl) ⟨1250619, by rfl⟩ : syracuseStep 3334985 = 2501239) B2501239
theorem B2220983 : Blo 984595 2220983 := bstep (se 1 (by rfl) ⟨1665737, by rfl⟩ : syracuseStep 2220983 = 3331475) B3331475
theorem B13493267 : Blo 984595 13493267 := bstep (se 1 (by rfl) ⟨10119950, by rfl⟩ : syracuseStep 13493267 = 20239901) B20239901
theorem B1664057 : Blo 984595 1664057 := bstep (se 2 (by rfl) ⟨624021, by rfl⟩ : syracuseStep 1664057 = 1248043) B1248043
theorem B60646553 : Blo 984595 60646553 := bstep (se 2 (by rfl) ⟨22742457, by rfl⟩ : syracuseStep 60646553 = 45484915) B45484915
theorem B6743411 : Blo 984595 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B2221577 : Blo 984595 2221577 := bstep (se 2 (by rfl) ⟨833091, by rfl⟩ : syracuseStep 2221577 = 1666183) B1666183
theorem B1664759 : Blo 984595 1664759 := bstep (se 1 (by rfl) ⟨1248569, by rfl⟩ : syracuseStep 1664759 = 2497139) B2497139
theorem B2811743 : Blo 984595 2811743 := bstep (se 1 (by rfl) ⟨2108807, by rfl⟩ : syracuseStep 2811743 = 4217615) B4217615
theorem B2221919 : Blo 984595 2221919 := bstep (se 1 (by rfl) ⟨1666439, by rfl⟩ : syracuseStep 2221919 = 3332879) B3332879
theorem B3336119 : Blo 984595 3336119 := bstep (se 1 (by rfl) ⟨2502089, by rfl⟩ : syracuseStep 3336119 = 5004179) B5004179
theorem B1107931 : Blo 984595 1107931 := bstep (se 1 (by rfl) ⟨830948, by rfl⟩ : syracuseStep 1107931 = 1661897) B1661897
theorem B7989263 : Blo 984595 7989263 := bstep (se 1 (by rfl) ⟨5991947, by rfl⟩ : syracuseStep 7989263 = 11983895) B11983895
theorem B2222099 : Blo 984595 2222099 := bstep (se 1 (by rfl) ⟨1666574, by rfl⟩ : syracuseStep 2222099 = 3333149) B3333149
theorem B3598415 : Blo 984595 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B1665103 : Blo 984595 1665103 := bstep (se 1 (by rfl) ⟨1248827, by rfl⟩ : syracuseStep 1665103 = 2497655) B2497655
theorem B1665353 : Blo 984595 1665353 := bstep (se 2 (by rfl) ⟨624507, by rfl⟩ : syracuseStep 1665353 = 1249015) B1249015
theorem B2222441 : Blo 984595 2222441 := bstep (se 2 (by rfl) ⟨833415, by rfl⟩ : syracuseStep 2222441 = 1666831) B1666831
theorem B1108399 : Blo 984595 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B1501735 : Blo 984595 1501735 := bstep (se 1 (by rfl) ⟨1126301, by rfl⟩ : syracuseStep 1501735 = 2252603) B2252603
theorem B16017965 : Blo 984595 16017965 := bstep (se 3 (by rfl) ⟨3003368, by rfl⟩ : syracuseStep 16017965 = 6006737) B6006737
theorem B3369595 : Blo 984595 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1665785 : Blo 984595 1665785 := bstep (se 2 (by rfl) ⟨624669, by rfl⟩ : syracuseStep 1665785 = 1249339) B1249339
theorem B2812745 : Blo 984595 2812745 := bstep (se 2 (by rfl) ⟨1054779, by rfl⟩ : syracuseStep 2812745 = 2109559) B2109559
theorem B1108831 : Blo 984595 1108831 := bstep (se 1 (by rfl) ⟨831623, by rfl⟩ : syracuseStep 1108831 = 1663247) B1663247
theorem B1665967 : Blo 984595 1665967 := bstep (se 1 (by rfl) ⟨1249475, by rfl⟩ : syracuseStep 1665967 = 2498951) B2498951
theorem B1895351 : Blo 984595 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B2223035 : Blo 984595 2223035 := bstep (se 1 (by rfl) ⟨1667276, by rfl⟩ : syracuseStep 2223035 = 3334553) B3334553
theorem B1666055 : Blo 984595 1666055 := bstep (se 1 (by rfl) ⟨1249541, by rfl⟩ : syracuseStep 1666055 = 2499083) B2499083
theorem B2223161 : Blo 984595 2223161 := bstep (se 2 (by rfl) ⟨833685, by rfl⟩ : syracuseStep 2223161 = 1667371) B1667371
theorem B16870517 : Blo 984595 16870517 := bstep (se 5 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 16870517 = 1581611) B1581611
theorem B1109191 : Blo 984595 1109191 := bstep (se 1 (by rfl) ⟨831893, by rfl⟩ : syracuseStep 1109191 = 1663787) B1663787
theorem B1666399 : Blo 984595 1666399 := bstep (se 1 (by rfl) ⟨1249799, by rfl⟩ : syracuseStep 1666399 = 2499599) B2499599
theorem B9006461 : Blo 984595 9006461 := bstep (se 3 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 9006461 = 3377423) B3377423
theorem B2223503 : Blo 984595 2223503 := bstep (se 1 (by rfl) ⟨1667627, by rfl⟩ : syracuseStep 2223503 = 3335255) B3335255
theorem B1666487 : Blo 984595 1666487 := bstep (se 1 (by rfl) ⟨1249865, by rfl⟩ : syracuseStep 1666487 = 2499731) B2499731
theorem B13495895 : Blo 984595 13495895 := bstep (se 1 (by rfl) ⟨10121921, by rfl⟩ : syracuseStep 13495895 = 20243843) B20243843
theorem B2223827 : Blo 984595 2223827 := bstep (se 1 (by rfl) ⟨1667870, by rfl⟩ : syracuseStep 2223827 = 3335741) B3335741
theorem B8548129 : Blo 984595 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B6320065 : Blo 984595 6320065 := bstep (se 2 (by rfl) ⟨2370024, by rfl⟩ : syracuseStep 6320065 = 4740049) B4740049
theorem B1667081 : Blo 984595 1667081 := bstep (se 2 (by rfl) ⟨625155, by rfl⟩ : syracuseStep 1667081 = 1250311) B1250311
theorem B10678301 : Blo 984595 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B1110055 : Blo 984595 1110055 := bstep (se 1 (by rfl) ⟨832541, by rfl⟩ : syracuseStep 1110055 = 1665083) B1665083
theorem B3600463 : Blo 984595 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B2814031 : Blo 984595 2814031 := bstep (se 1 (by rfl) ⟨2110523, by rfl⟩ : syracuseStep 2814031 = 4221047) B4221047
theorem B1667243 : Blo 984595 1667243 := bstep (se 1 (by rfl) ⟨1250432, by rfl⟩ : syracuseStep 1667243 = 2500865) B2500865
theorem B1405279 : Blo 984595 1405279 := bstep (se 1 (by rfl) ⟨1053959, by rfl⟩ : syracuseStep 1405279 = 2107919) B2107919
theorem B1667641 : Blo 984595 1667641 := bstep (se 2 (by rfl) ⟨625365, by rfl⟩ : syracuseStep 1667641 = 1250731) B1250731
theorem B1667783 : Blo 984595 1667783 := bstep (se 1 (by rfl) ⟨1250837, by rfl⟩ : syracuseStep 1667783 = 2501675) B2501675
theorem B1667945 : Blo 984595 1667945 := bstep (se 2 (by rfl) ⟨625479, by rfl⟩ : syracuseStep 1667945 = 1250959) B1250959
theorem B3994795 : Blo 984595 3994795 := bstep (se 1 (by rfl) ⟨2996096, by rfl⟩ : syracuseStep 3994795 = 5992193) B5992193
theorem B28407185 : Blo 984595 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B7501409 : Blo 984595 7501409 := bstep (se 2 (by rfl) ⟨2813028, by rfl⟩ : syracuseStep 7501409 = 5626057) B5626057
theorem B1111675 : Blo 984595 1111675 := bstep (se 1 (by rfl) ⟨833756, by rfl⟩ : syracuseStep 1111675 = 1667513) B1667513
theorem B7108229 : Blo 984595 7108229 := bstep (se 4 (by rfl) ⟨666396, by rfl⟩ : syracuseStep 7108229 = 1332793) B1332793
theorem B1996537 : Blo 984595 1996537 := bstep (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) B1497403
theorem B1112143 : Blo 984595 1112143 := bstep (se 1 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 1112143 = 1668215) B1668215
theorem B3995801 : Blo 984595 3995801 := bstep (se 2 (by rfl) ⟨1498425, by rfl⟩ : syracuseStep 3995801 = 2996851) B2996851
theorem B7109153 : Blo 984595 7109153 := bstep (se 2 (by rfl) ⟨2665932, by rfl⟩ : syracuseStep 7109153 = 5331865) B5331865
theorem B4750255 : Blo 984595 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B7502867 : Blo 984595 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B5996231 : Blo 984595 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B9469831 : Blo 984595 9469831 := bstep (se 1 (by rfl) ⟨7102373, by rfl⟩ : syracuseStep 9469831 = 14204747) B14204747
theorem B14221241 : Blo 984595 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B62357521 : Blo 984595 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B2195819 : Blo 984595 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B20283833 : Blo 984595 20283833 := bstep (se 2 (by rfl) ⟨7606437, by rfl⟩ : syracuseStep 20283833 = 15212875) B15212875
theorem B32440933 : Blo 984595 32440933 := bstep (se 4 (by rfl) ⟨3041337, by rfl⟩ : syracuseStep 32440933 = 6082675) B6082675
theorem B18220439 : Blo 984595 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B3999289 : Blo 984595 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B984639 : Blo 984595 984639 := bstep (se 1 (by rfl) ⟨738479, by rfl⟩ : syracuseStep 984639 = 1476959) B1476959
theorem B984647 : Blo 984595 984647 := bstep (se 1 (by rfl) ⟨738485, by rfl⟩ : syracuseStep 984647 = 1476971) B1476971
theorem B984799 : Blo 984595 984799 := bstep (se 1 (by rfl) ⟨738599, by rfl⟩ : syracuseStep 984799 = 1477199) B1477199
theorem B984879 : Blo 984595 984879 := bstep (se 1 (by rfl) ⟨738659, by rfl⟩ : syracuseStep 984879 = 1477319) B1477319
theorem B984987 : Blo 984595 984987 := bstep (se 1 (by rfl) ⟨738740, by rfl⟩ : syracuseStep 984987 = 1477481) B1477481
theorem B105514913 : Blo 984595 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B985039 : Blo 984595 985039 := bstep (se 1 (by rfl) ⟨738779, by rfl⟩ : syracuseStep 985039 = 1477559) B1477559
theorem B985063 : Blo 984595 985063 := bstep (se 1 (by rfl) ⟨738797, by rfl⟩ : syracuseStep 985063 = 1477595) B1477595
theorem B2492441 : Blo 984595 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B985375 : Blo 984595 985375 := bstep (se 1 (by rfl) ⟨739031, by rfl⟩ : syracuseStep 985375 = 1478063) B1478063
theorem B985435 : Blo 984595 985435 := bstep (se 1 (by rfl) ⟨739076, by rfl⟩ : syracuseStep 985435 = 1478153) B1478153
theorem B985455 : Blo 984595 985455 := bstep (se 1 (by rfl) ⟨739091, by rfl⟩ : syracuseStep 985455 = 1478183) B1478183
theorem B1477031 : Blo 984595 1477031 := bstep (se 1 (by rfl) ⟨1107773, by rfl⟩ : syracuseStep 1477031 = 2215547) B2215547
theorem B985511 : Blo 984595 985511 := bstep (se 1 (by rfl) ⟨739133, by rfl⟩ : syracuseStep 985511 = 1478267) B1478267
theorem B3803603 : Blo 984595 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B1477115 : Blo 984595 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B985595 : Blo 984595 985595 := bstep (se 1 (by rfl) ⟨739196, by rfl⟩ : syracuseStep 985595 = 1478393) B1478393
theorem B985663 : Blo 984595 985663 := bstep (se 1 (by rfl) ⟨739247, by rfl⟩ : syracuseStep 985663 = 1478495) B1478495
theorem B985671 : Blo 984595 985671 := bstep (se 1 (by rfl) ⟨739253, by rfl⟩ : syracuseStep 985671 = 1478507) B1478507
theorem B1247815 : Blo 984595 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B1477241 : Blo 984595 1477241 := bstep (se 2 (by rfl) ⟨553965, by rfl⟩ : syracuseStep 1477241 = 1107931) B1107931
theorem B1477295 : Blo 984595 1477295 := bstep (se 1 (by rfl) ⟨1107971, by rfl⟩ : syracuseStep 1477295 = 2215943) B2215943
theorem B1477343 : Blo 984595 1477343 := bstep (se 1 (by rfl) ⟨1108007, by rfl⟩ : syracuseStep 1477343 = 2216015) B2216015
theorem B985823 : Blo 984595 985823 := bstep (se 1 (by rfl) ⟨739367, by rfl⟩ : syracuseStep 985823 = 1478735) B1478735
theorem B985903 : Blo 984595 985903 := bstep (se 1 (by rfl) ⟨739427, by rfl⟩ : syracuseStep 985903 = 1478855) B1478855
theorem B7506755 : Blo 984595 7506755 := bstep (se 1 (by rfl) ⟨5630066, by rfl⟩ : syracuseStep 7506755 = 11260133) B11260133
theorem B986011 : Blo 984595 986011 := bstep (se 1 (by rfl) ⟨739508, by rfl⟩ : syracuseStep 986011 = 1479017) B1479017
theorem B986063 : Blo 984595 986063 := bstep (se 1 (by rfl) ⟨739547, by rfl⟩ : syracuseStep 986063 = 1479095) B1479095
theorem B1477607 : Blo 984595 1477607 := bstep (se 1 (by rfl) ⟨1108205, by rfl⟩ : syracuseStep 1477607 = 2216411) B2216411
theorem B986087 : Blo 984595 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B12651659 : Blo 984595 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B1477865 : Blo 984595 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1477919 : Blo 984595 1477919 := bstep (se 1 (by rfl) ⟨1108439, by rfl⟩ : syracuseStep 1477919 = 2216879) B2216879
theorem B986399 : Blo 984595 986399 := bstep (se 1 (by rfl) ⟨739799, by rfl⟩ : syracuseStep 986399 = 1479599) B1479599
theorem B986459 : Blo 984595 986459 := bstep (se 1 (by rfl) ⟨739844, by rfl⟩ : syracuseStep 986459 = 1479689) B1479689
theorem B986479 : Blo 984595 986479 := bstep (se 1 (by rfl) ⟨739859, by rfl⟩ : syracuseStep 986479 = 1479719) B1479719
theorem B1248635 : Blo 984595 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B2002313 : Blo 984595 2002313 := bstep (se 2 (by rfl) ⟨750867, by rfl⟩ : syracuseStep 2002313 = 1501735) B1501735
theorem B986535 : Blo 984595 986535 := bstep (se 1 (by rfl) ⟨739901, by rfl⟩ : syracuseStep 986535 = 1479803) B1479803
theorem B1478087 : Blo 984595 1478087 := bstep (se 1 (by rfl) ⟨1108565, by rfl⟩ : syracuseStep 1478087 = 2217131) B2217131
theorem B4492793 : Blo 984595 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B986619 : Blo 984595 986619 := bstep (se 1 (by rfl) ⟨739964, by rfl⟩ : syracuseStep 986619 = 1479929) B1479929
theorem B986687 : Blo 984595 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B986695 : Blo 984595 986695 := bstep (se 1 (by rfl) ⟨740021, by rfl⟩ : syracuseStep 986695 = 1480043) B1480043
theorem B986847 : Blo 984595 986847 := bstep (se 1 (by rfl) ⟨740135, by rfl⟩ : syracuseStep 986847 = 1480271) B1480271
theorem B1478441 : Blo 984595 1478441 := bstep (se 2 (by rfl) ⟨554415, by rfl⟩ : syracuseStep 1478441 = 1108831) B1108831
theorem B1478447 : Blo 984595 1478447 := bstep (se 1 (by rfl) ⟨1108835, by rfl⟩ : syracuseStep 1478447 = 2217671) B2217671
theorem B986927 : Blo 984595 986927 := bstep (se 1 (by rfl) ⟨740195, by rfl⟩ : syracuseStep 986927 = 1480391) B1480391
theorem B7212847 : Blo 984595 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B987035 : Blo 984595 987035 := bstep (se 1 (by rfl) ⟨740276, by rfl⟩ : syracuseStep 987035 = 1480553) B1480553
theorem B2494415 : Blo 984595 2494415 := bstep (se 1 (by rfl) ⟨1870811, by rfl⟩ : syracuseStep 2494415 = 3741623) B3741623
theorem B987087 : Blo 984595 987087 := bstep (se 1 (by rfl) ⟨740315, by rfl⟩ : syracuseStep 987087 = 1480631) B1480631
theorem B987111 : Blo 984595 987111 := bstep (se 1 (by rfl) ⟨740333, by rfl⟩ : syracuseStep 987111 = 1480667) B1480667
theorem B1478921 : Blo 984595 1478921 := bstep (se 2 (by rfl) ⟨554595, by rfl⟩ : syracuseStep 1478921 = 1109191) B1109191
theorem B987423 : Blo 984595 987423 := bstep (se 1 (by rfl) ⟨740567, by rfl⟩ : syracuseStep 987423 = 1481135) B1481135
theorem B987483 : Blo 984595 987483 := bstep (se 1 (by rfl) ⟨740612, by rfl⟩ : syracuseStep 987483 = 1481225) B1481225
theorem B1479023 : Blo 984595 1479023 := bstep (se 1 (by rfl) ⟨1109267, by rfl⟩ : syracuseStep 1479023 = 2218535) B2218535
theorem B987503 : Blo 984595 987503 := bstep (se 1 (by rfl) ⟨740627, by rfl⟩ : syracuseStep 987503 = 1481255) B1481255
theorem B1184167 : Blo 984595 1184167 := bstep (se 1 (by rfl) ⟨888125, by rfl⟩ : syracuseStep 1184167 = 1776251) B1776251
theorem B987559 : Blo 984595 987559 := bstep (se 1 (by rfl) ⟨740669, by rfl⟩ : syracuseStep 987559 = 1481339) B1481339
theorem B987643 : Blo 984595 987643 := bstep (se 1 (by rfl) ⟨740732, by rfl⟩ : syracuseStep 987643 = 1481465) B1481465
theorem B987711 : Blo 984595 987711 := bstep (se 1 (by rfl) ⟨740783, by rfl⟩ : syracuseStep 987711 = 1481567) B1481567
theorem B1479239 : Blo 984595 1479239 := bstep (se 1 (by rfl) ⟨1109429, by rfl⟩ : syracuseStep 1479239 = 2218859) B2218859
theorem B987719 : Blo 984595 987719 := bstep (se 1 (by rfl) ⟨740789, by rfl⟩ : syracuseStep 987719 = 1481579) B1481579
theorem B2495083 : Blo 984595 2495083 := bstep (se 1 (by rfl) ⟨1871312, by rfl⟩ : syracuseStep 2495083 = 3742625) B3742625
theorem B1184363 : Blo 984595 1184363 := bstep (se 1 (by rfl) ⟨888272, by rfl⟩ : syracuseStep 1184363 = 1776545) B1776545
theorem B1479275 : Blo 984595 1479275 := bstep (se 1 (by rfl) ⟨1109456, by rfl⟩ : syracuseStep 1479275 = 2218913) B2218913
theorem B14389913 : Blo 984595 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B987871 : Blo 984595 987871 := bstep (se 1 (by rfl) ⟨740903, by rfl⟩ : syracuseStep 987871 = 1481807) B1481807
theorem B987951 : Blo 984595 987951 := bstep (se 1 (by rfl) ⟨740963, by rfl⟩ : syracuseStep 987951 = 1481927) B1481927
theorem B1479503 : Blo 984595 1479503 := bstep (se 1 (by rfl) ⟨1109627, by rfl⟩ : syracuseStep 1479503 = 2219255) B2219255
theorem B2495387 : Blo 984595 2495387 := bstep (se 1 (by rfl) ⟨1871540, by rfl⟩ : syracuseStep 2495387 = 3743081) B3743081
theorem B988059 : Blo 984595 988059 := bstep (se 1 (by rfl) ⟨741044, by rfl⟩ : syracuseStep 988059 = 1482089) B1482089
theorem B32478155 : Blo 984595 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B1250255 : Blo 984595 1250255 := bstep (se 1 (by rfl) ⟨937691, by rfl⟩ : syracuseStep 1250255 = 1875383) B1875383
theorem B988111 : Blo 984595 988111 := bstep (se 1 (by rfl) ⟨741083, by rfl⟩ : syracuseStep 988111 = 1482167) B1482167
theorem B988135 : Blo 984595 988135 := bstep (se 1 (by rfl) ⟨741101, by rfl⟩ : syracuseStep 988135 = 1482203) B1482203
theorem B1479899 : Blo 984595 1479899 := bstep (se 1 (by rfl) ⟨1109924, by rfl⟩ : syracuseStep 1479899 = 2219849) B2219849
theorem B2495731 : Blo 984595 2495731 := bstep (se 1 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 2495731 = 3743597) B3743597
theorem B8426753 : Blo 984595 8426753 := bstep (se 2 (by rfl) ⟨3160032, by rfl⟩ : syracuseStep 8426753 = 6320065) B6320065
theorem B988447 : Blo 984595 988447 := bstep (se 1 (by rfl) ⟨741335, by rfl⟩ : syracuseStep 988447 = 1482671) B1482671
theorem B988507 : Blo 984595 988507 := bstep (se 1 (by rfl) ⟨741380, by rfl⟩ : syracuseStep 988507 = 1482761) B1482761
theorem B988527 : Blo 984595 988527 := bstep (se 1 (by rfl) ⟨741395, by rfl⟩ : syracuseStep 988527 = 1482791) B1482791
theorem B1480073 : Blo 984595 1480073 := bstep (se 2 (by rfl) ⟨555027, by rfl⟩ : syracuseStep 1480073 = 1110055) B1110055
theorem B988583 : Blo 984595 988583 := bstep (se 1 (by rfl) ⟨741437, by rfl⟩ : syracuseStep 988583 = 1482875) B1482875
theorem B1709561 : Blo 984595 1709561 := bstep (se 2 (by rfl) ⟨641085, by rfl⟩ : syracuseStep 1709561 = 1282171) B1282171
theorem B1480427 : Blo 984595 1480427 := bstep (se 1 (by rfl) ⟨1110320, by rfl⟩ : syracuseStep 1480427 = 2220641) B2220641
theorem B1873705 : Blo 984595 1873705 := bstep (se 2 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 1873705 = 1405279) B1405279
theorem B1480655 : Blo 984595 1480655 := bstep (se 1 (by rfl) ⟨1110491, by rfl⟩ : syracuseStep 1480655 = 2220983) B2220983
theorem B2496521 : Blo 984595 2496521 := bstep (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) B1872391
theorem B166205573 : Blo 984595 166205573 := bstep (se 4 (by rfl) ⟨15581772, by rfl⟩ : syracuseStep 166205573 = 31163545) B31163545
theorem B4495607 : Blo 984595 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B1481051 : Blo 984595 1481051 := bstep (se 1 (by rfl) ⟨1110788, by rfl⟩ : syracuseStep 1481051 = 2221577) B2221577
theorem B1874495 : Blo 984595 1874495 := bstep (se 1 (by rfl) ⟨1405871, by rfl⟩ : syracuseStep 1874495 = 2811743) B2811743
theorem B1481279 : Blo 984595 1481279 := bstep (se 1 (by rfl) ⟨1110959, by rfl⟩ : syracuseStep 1481279 = 2221919) B2221919
theorem B2103887 : Blo 984595 2103887 := bstep (se 1 (by rfl) ⟨1577915, by rfl⟩ : syracuseStep 2103887 = 3155831) B3155831
theorem B1481399 : Blo 984595 1481399 := bstep (se 1 (by rfl) ⟨1111049, by rfl⟩ : syracuseStep 1481399 = 2222099) B2222099
theorem B2398943 : Blo 984595 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B2104031 : Blo 984595 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B1776539 : Blo 984595 1776539 := bstep (se 1 (by rfl) ⟨1332404, by rfl⟩ : syracuseStep 1776539 = 2664809) B2664809
theorem B1481627 : Blo 984595 1481627 := bstep (se 1 (by rfl) ⟨1111220, by rfl⟩ : syracuseStep 1481627 = 2222441) B2222441
theorem B2497675 : Blo 984595 2497675 := bstep (se 1 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 2497675 = 3746513) B3746513
theorem B1875163 : Blo 984595 1875163 := bstep (se 1 (by rfl) ⟨1406372, by rfl⟩ : syracuseStep 1875163 = 2812745) B2812745
theorem B1482023 : Blo 984595 1482023 := bstep (se 1 (by rfl) ⟨1111517, by rfl⟩ : syracuseStep 1482023 = 2223035) B2223035
theorem B1482107 : Blo 984595 1482107 := bstep (se 1 (by rfl) ⟨1111580, by rfl⟩ : syracuseStep 1482107 = 2223161) B2223161
theorem B11247011 : Blo 984595 11247011 := bstep (se 1 (by rfl) ⟨8435258, by rfl⟩ : syracuseStep 11247011 = 16870517) B16870517
theorem B2497979 : Blo 984595 2497979 := bstep (se 1 (by rfl) ⟨1873484, by rfl⟩ : syracuseStep 2497979 = 3746969) B3746969
theorem B2104775 : Blo 984595 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B1482233 : Blo 984595 1482233 := bstep (se 2 (by rfl) ⟨555837, by rfl⟩ : syracuseStep 1482233 = 1111675) B1111675
theorem B6004307 : Blo 984595 6004307 := bstep (se 1 (by rfl) ⟨4503230, by rfl⟩ : syracuseStep 6004307 = 9006461) B9006461
theorem B1482335 : Blo 984595 1482335 := bstep (se 1 (by rfl) ⟨1111751, by rfl⟩ : syracuseStep 1482335 = 2223503) B2223503
theorem B2662049 : Blo 984595 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B4988627 : Blo 984595 4988627 := bstep (se 1 (by rfl) ⟨3741470, by rfl⟩ : syracuseStep 4988627 = 7482941) B7482941
theorem B1482551 : Blo 984595 1482551 := bstep (se 1 (by rfl) ⟨1111913, by rfl⟩ : syracuseStep 1482551 = 2223827) B2223827
theorem B2662301 : Blo 984595 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B7118867 : Blo 984595 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B1482857 : Blo 984595 1482857 := bstep (se 2 (by rfl) ⟨556071, by rfl⟩ : syracuseStep 1482857 = 1112143) B1112143
theorem B4989275 : Blo 984595 4989275 := bstep (se 1 (by rfl) ⟨3741956, by rfl⟩ : syracuseStep 4989275 = 7483913) B7483913
theorem B2368073 : Blo 984595 2368073 := bstep (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) B1776055
theorem B1581689 : Blo 984595 1581689 := bstep (se 2 (by rfl) ⟨593133, by rfl⟩ : syracuseStep 1581689 = 1186267) B1186267
theorem B2499295 : Blo 984595 2499295 := bstep (se 1 (by rfl) ⟨1874471, by rfl⟩ : syracuseStep 2499295 = 3748943) B3748943
theorem B2499407 : Blo 984595 2499407 := bstep (se 1 (by rfl) ⟨1874555, by rfl⟩ : syracuseStep 2499407 = 3749111) B3749111
theorem B2368487 : Blo 984595 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B17966069 : Blo 984595 17966069 := bstep (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) B1684319
theorem B2106491 : Blo 984595 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B6333673 : Blo 984595 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B4990247 : Blo 984595 4990247 := bstep (se 1 (by rfl) ⟨3742685, by rfl⟩ : syracuseStep 4990247 = 7485371) B7485371
theorem B2663867 : Blo 984595 2663867 := bstep (se 1 (by rfl) ⟨1997900, by rfl⟩ : syracuseStep 2663867 = 3995801) B3995801
theorem B2500055 : Blo 984595 2500055 := bstep (se 1 (by rfl) ⟨1875041, by rfl⟩ : syracuseStep 2500055 = 3750083) B3750083
theorem B2500409 : Blo 984595 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B1779977 : Blo 984595 1779977 := bstep (se 2 (by rfl) ⟨667491, by rfl⟩ : syracuseStep 1779977 = 1334983) B1334983
theorem B1780193 : Blo 984595 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B12626441 : Blo 984595 12626441 := bstep (se 2 (by rfl) ⟨4734915, by rfl⟩ : syracuseStep 12626441 = 9469831) B9469831
theorem B9480827 : Blo 984595 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B6761083 : Blo 984595 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B6007517 : Blo 984595 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B8006525 : Blo 984595 8006525 := bstep (se 3 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 8006525 = 3002447) B3002447
theorem B2403425 : Blo 984595 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B4992353 : Blo 984595 4992353 := bstep (se 2 (by rfl) ⟨1872132, by rfl⟩ : syracuseStep 4992353 = 3744265) B3744265
theorem B2370977 : Blo 984595 2370977 := bstep (se 2 (by rfl) ⟨889116, by rfl⟩ : syracuseStep 2370977 = 1778233) B1778233
theorem B2502049 : Blo 984595 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B2371457 : Blo 984595 2371457 := bstep (se 2 (by rfl) ⟨889296, by rfl⟩ : syracuseStep 2371457 = 1778593) B1778593
theorem B13512653 : Blo 984595 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B4206593 : Blo 984595 4206593 := bstep (se 2 (by rfl) ⟨1577472, by rfl⟩ : syracuseStep 4206593 = 3154945) B3154945
theorem B11383055 : Blo 984595 11383055 := bstep (se 1 (by rfl) ⟨8537291, by rfl⟩ : syracuseStep 11383055 = 17074583) B17074583
theorem B16003433 : Blo 984595 16003433 := bstep (se 2 (by rfl) ⟨6001287, by rfl⟩ : syracuseStep 16003433 = 12002575) B12002575
theorem B4994297 : Blo 984595 4994297 := bstep (se 2 (by rfl) ⟨1872861, by rfl⟩ : syracuseStep 4994297 = 3745723) B3745723
theorem B3323753 : Blo 984595 3323753 := bstep (se 2 (by rfl) ⟨1246407, by rfl⟩ : syracuseStep 3323753 = 2492815) B2492815
theorem B3160097 : Blo 984595 3160097 := bstep (se 2 (by rfl) ⟨1185036, by rfl⟩ : syracuseStep 3160097 = 2370073) B2370073
theorem B3553465 : Blo 984595 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B3324185 : Blo 984595 3324185 := bstep (se 2 (by rfl) ⟨1246569, by rfl⟩ : syracuseStep 3324185 = 2493139) B2493139
theorem B16857395 : Blo 984595 16857395 := bstep (se 1 (by rfl) ⟨12643046, by rfl⟩ : syracuseStep 16857395 = 25286093) B25286093
theorem B4209191 : Blo 984595 4209191 := bstep (se 1 (by rfl) ⟨3156893, by rfl⟩ : syracuseStep 4209191 = 6313787) B6313787
theorem B8436899 : Blo 984595 8436899 := bstep (se 1 (by rfl) ⟨6327674, by rfl⟩ : syracuseStep 8436899 = 12655349) B12655349
theorem B3161531 : Blo 984595 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B3325535 : Blo 984595 3325535 := bstep (se 1 (by rfl) ⟨2494151, by rfl⟩ : syracuseStep 3325535 = 4988303) B4988303
theorem B8011649 : Blo 984595 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B4800617 : Blo 984595 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B3752041 : Blo 984595 3752041 := bstep (se 2 (by rfl) ⟨1407015, by rfl⟩ : syracuseStep 3752041 = 2814031) B2814031
theorem B5325011 : Blo 984595 5325011 := bstep (se 1 (by rfl) ⟨3993758, by rfl⟩ : syracuseStep 5325011 = 7987517) B7987517
theorem B5620225 : Blo 984595 5620225 := bstep (se 2 (by rfl) ⟨2107584, by rfl⟩ : syracuseStep 5620225 = 4215169) B4215169
theorem B2671177 : Blo 984595 2671177 := bstep (se 2 (by rfl) ⟨1001691, by rfl⟩ : syracuseStep 2671177 = 2003383) B2003383
theorem B8995511 : Blo 984595 8995511 := bstep (se 1 (by rfl) ⟨6746633, by rfl⟩ : syracuseStep 8995511 = 13493267) B13493267
theorem B2671327 : Blo 984595 2671327 := bstep (se 1 (by rfl) ⟨2003495, by rfl⟩ : syracuseStep 2671327 = 4006991) B4006991
theorem B3326939 : Blo 984595 3326939 := bstep (se 1 (by rfl) ⟨2495204, by rfl⟩ : syracuseStep 3326939 = 4990409) B4990409
theorem B3327101 : Blo 984595 3327101 := bstep (se 3 (by rfl) ⟨623831, by rfl⟩ : syracuseStep 3327101 = 1247663) B1247663
theorem B3327209 : Blo 984595 3327209 := bstep (se 2 (by rfl) ⟨1247703, by rfl⟩ : syracuseStep 3327209 = 2495407) B2495407
theorem B5326175 : Blo 984595 5326175 := bstep (se 1 (by rfl) ⟨3994631, by rfl⟩ : syracuseStep 5326175 = 7989263) B7989263
theorem B4998509 : Blo 984595 4998509 := bstep (se 3 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 4998509 = 1874441) B1874441
theorem B3327371 : Blo 984595 3327371 := bstep (se 1 (by rfl) ⟨2495528, by rfl⟩ : syracuseStep 3327371 = 4991057) B4991057
theorem B5326393 : Blo 984595 5326393 := bstep (se 2 (by rfl) ⟨1997397, by rfl⟩ : syracuseStep 5326393 = 3994795) B3994795
theorem B8439497 : Blo 984595 8439497 := bstep (se 2 (by rfl) ⟨3164811, by rfl⟩ : syracuseStep 8439497 = 6329623) B6329623
theorem B6309737 : Blo 984595 6309737 := bstep (se 2 (by rfl) ⟨2366151, by rfl⟩ : syracuseStep 6309737 = 4732303) B4732303
theorem B10111169 : Blo 984595 10111169 := bstep (se 2 (by rfl) ⟨3791688, by rfl⟩ : syracuseStep 10111169 = 7583377) B7583377
theorem B8997263 : Blo 984595 8997263 := bstep (se 1 (by rfl) ⟨6747947, by rfl⟩ : syracuseStep 8997263 = 13495895) B13495895
theorem B2804179 : Blo 984595 2804179 := bstep (se 1 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 2804179 = 4206269) B4206269
theorem B6408791 : Blo 984595 6408791 := bstep (se 1 (by rfl) ⟨4806593, by rfl⟩ : syracuseStep 6408791 = 9613187) B9613187
theorem B2215367 : Blo 984595 2215367 := bstep (se 1 (by rfl) ⟨1661525, by rfl⟩ : syracuseStep 2215367 = 3323051) B3323051
theorem B4214281 : Blo 984595 4214281 := bstep (se 2 (by rfl) ⟨1580355, by rfl⟩ : syracuseStep 4214281 = 3160711) B3160711
theorem B5000939 : Blo 984595 5000939 := bstep (se 1 (by rfl) ⟨3750704, by rfl⟩ : syracuseStep 5000939 = 7501409) B7501409
theorem B4738819 : Blo 984595 4738819 := bstep (se 1 (by rfl) ⟨3554114, by rfl⟩ : syracuseStep 4738819 = 7108229) B7108229
theorem B2805511 : Blo 984595 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B2215727 : Blo 984595 2215727 := bstep (se 1 (by rfl) ⟨1661795, by rfl⟩ : syracuseStep 2215727 = 3323591) B3323591
theorem B2805785 : Blo 984595 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B7491689 : Blo 984595 7491689 := bstep (se 2 (by rfl) ⟨2809383, by rfl⟩ : syracuseStep 7491689 = 5618767) B5618767
theorem B10145897 : Blo 984595 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B5001425 : Blo 984595 5001425 := bstep (se 2 (by rfl) ⟨1875534, by rfl⟩ : syracuseStep 5001425 = 3751069) B3751069
theorem B10670339 : Blo 984595 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B3330395 : Blo 984595 3330395 := bstep (se 1 (by rfl) ⟨2497796, by rfl⟩ : syracuseStep 3330395 = 4995593) B4995593
theorem B4739435 : Blo 984595 4739435 := bstep (se 1 (by rfl) ⟨3554576, by rfl⟩ : syracuseStep 4739435 = 7109153) B7109153
theorem B2216303 : Blo 984595 2216303 := bstep (se 1 (by rfl) ⟨1662227, by rfl⟩ : syracuseStep 2216303 = 3324455) B3324455
theorem B2216375 : Blo 984595 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B2216519 : Blo 984595 2216519 := bstep (se 1 (by rfl) ⟨1662389, by rfl⟩ : syracuseStep 2216519 = 3324779) B3324779
theorem B5624417 : Blo 984595 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B2216555 : Blo 984595 2216555 := bstep (se 1 (by rfl) ⟨1662416, by rfl⟩ : syracuseStep 2216555 = 3324833) B3324833
theorem B5001911 : Blo 984595 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B2216951 : Blo 984595 2216951 := bstep (se 1 (by rfl) ⟨1662713, by rfl⟩ : syracuseStep 2216951 = 3325427) B3325427
theorem B4740221 : Blo 984595 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B3560573 : Blo 984595 3560573 := bstep (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) B1335215
theorem B5002397 : Blo 984595 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B3331367 : Blo 984595 3331367 := bstep (se 1 (by rfl) ⟨2498525, by rfl⟩ : syracuseStep 3331367 = 4997051) B4997051
theorem B2217311 : Blo 984595 2217311 := bstep (se 1 (by rfl) ⟨1662983, by rfl⟩ : syracuseStep 2217311 = 3325967) B3325967
theorem B9491975 : Blo 984595 9491975 := bstep (se 1 (by rfl) ⟨7118981, by rfl⟩ : syracuseStep 9491975 = 14237963) B14237963
theorem B1267375 : Blo 984595 1267375 := bstep (se 1 (by rfl) ⟨950531, by rfl⟩ : syracuseStep 1267375 = 1901063) B1901063
theorem B2217707 : Blo 984595 2217707 := bstep (se 1 (by rfl) ⟨1663280, by rfl⟩ : syracuseStep 2217707 = 3326561) B3326561
theorem B4216657 : Blo 984595 4216657 := bstep (se 2 (by rfl) ⟨1581246, by rfl⟩ : syracuseStep 4216657 = 3162493) B3162493
theorem B2217833 : Blo 984595 2217833 := bstep (se 2 (by rfl) ⟨831687, by rfl⟩ : syracuseStep 2217833 = 1663375) B1663375
theorem B1333199 : Blo 984595 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B3332231 : Blo 984595 3332231 := bstep (se 1 (by rfl) ⟨2499173, by rfl⟩ : syracuseStep 3332231 = 4998347) B4998347
theorem B10115351 : Blo 984595 10115351 := bstep (se 1 (by rfl) ⟨7586513, by rfl⟩ : syracuseStep 10115351 = 15173027) B15173027
theorem B8444249 : Blo 984595 8444249 := bstep (se 2 (by rfl) ⟨3166593, by rfl⟩ : syracuseStep 8444249 = 6333187) B6333187
theorem B4217255 : Blo 984595 4217255 := bstep (se 1 (by rfl) ⟨3162941, by rfl⟩ : syracuseStep 4217255 = 6325883) B6325883
theorem B5003693 : Blo 984595 5003693 := bstep (se 3 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 5003693 = 1876385) B1876385
theorem B20240891 : Blo 984595 20240891 := bstep (se 1 (by rfl) ⟨15180668, by rfl⟩ : syracuseStep 20240891 = 30361337) B30361337
theorem B1333831 : Blo 984595 1333831 := bstep (se 1 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 1333831 = 2000747) B2000747
theorem B5003855 : Blo 984595 5003855 := bstep (se 1 (by rfl) ⟨3752891, by rfl⟩ : syracuseStep 5003855 = 7505783) B7505783
theorem B2808427 : Blo 984595 2808427 := bstep (se 1 (by rfl) ⟨2106320, by rfl⟩ : syracuseStep 2808427 = 4212641) B4212641
theorem B2218679 : Blo 984595 2218679 := bstep (se 1 (by rfl) ⟨1664009, by rfl⟩ : syracuseStep 2218679 = 3328019) B3328019
theorem B3562231 : Blo 984595 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B2808701 : Blo 984595 2808701 := bstep (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) B1053263
theorem B2218895 : Blo 984595 2218895 := bstep (se 1 (by rfl) ⟨1664171, by rfl⟩ : syracuseStep 2218895 = 3328343) B3328343
theorem B12639563 : Blo 984595 12639563 := bstep (se 1 (by rfl) ⟨9479672, by rfl⟩ : syracuseStep 12639563 = 18959345) B18959345
theorem B3333473 : Blo 984595 3333473 := bstep (se 2 (by rfl) ⟨1250052, by rfl⟩ : syracuseStep 3333473 = 2500105) B2500105
theorem B1662457 : Blo 984595 1662457 := bstep (se 2 (by rfl) ⟨623421, by rfl⟩ : syracuseStep 1662457 = 1246843) B1246843
theorem B2219615 : Blo 984595 2219615 := bstep (se 1 (by rfl) ⟨1664711, by rfl⟩ : syracuseStep 2219615 = 3329423) B3329423
theorem B8216225 : Blo 984595 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B1662727 : Blo 984595 1662727 := bstep (se 1 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 1662727 = 2494091) B2494091
theorem B1662761 : Blo 984595 1662761 := bstep (se 2 (by rfl) ⟨623535, by rfl⟩ : syracuseStep 1662761 = 1247071) B1247071
theorem B2219831 : Blo 984595 2219831 := bstep (se 1 (by rfl) ⟨1664873, by rfl⟩ : syracuseStep 2219831 = 3329747) B3329747
theorem B2809657 : Blo 984595 2809657 := bstep (se 2 (by rfl) ⟨1053621, by rfl⟩ : syracuseStep 2809657 = 2107243) B2107243
theorem B2220137 : Blo 984595 2220137 := bstep (se 2 (by rfl) ⟨832551, by rfl⟩ : syracuseStep 2220137 = 1665103) B1665103
theorem B5988833 : Blo 984595 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B1663483 : Blo 984595 1663483 := bstep (se 1 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 1663483 = 2495225) B2495225
theorem B2220623 : Blo 984595 2220623 := bstep (se 1 (by rfl) ⟨1665467, by rfl⟩ : syracuseStep 2220623 = 3330935) B3330935
theorem B13001363 : Blo 984595 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B2220767 : Blo 984595 2220767 := bstep (se 1 (by rfl) ⟨1665575, by rfl⟩ : syracuseStep 2220767 = 3331151) B3331151
theorem B20243351 : Blo 984595 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B1663915 : Blo 984595 1663915 := bstep (se 1 (by rfl) ⟨1247936, by rfl⟩ : syracuseStep 1663915 = 2495873) B2495873
theorem B2221019 : Blo 984595 2221019 := bstep (se 1 (by rfl) ⟨1665764, by rfl⟩ : syracuseStep 2221019 = 3331529) B3331529
theorem B9495589 : Blo 984595 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B2221199 : Blo 984595 2221199 := bstep (se 1 (by rfl) ⟨1665899, by rfl⟩ : syracuseStep 2221199 = 3331799) B3331799
theorem B1664219 : Blo 984595 1664219 := bstep (se 1 (by rfl) ⟨1248164, by rfl⟩ : syracuseStep 1664219 = 2496329) B2496329
theorem B2221289 : Blo 984595 2221289 := bstep (se 2 (by rfl) ⟨832983, by rfl⟩ : syracuseStep 2221289 = 1665967) B1665967
theorem B3335417 : Blo 984595 3335417 := bstep (se 2 (by rfl) ⟨1250781, by rfl⟩ : syracuseStep 3335417 = 2501563) B2501563
theorem B2221343 : Blo 984595 2221343 := bstep (se 1 (by rfl) ⟨1666007, by rfl⟩ : syracuseStep 2221343 = 3332015) B3332015
theorem B1664455 : Blo 984595 1664455 := bstep (se 1 (by rfl) ⟨1248341, by rfl⟩ : syracuseStep 1664455 = 2496683) B2496683
theorem B3335687 : Blo 984595 3335687 := bstep (se 1 (by rfl) ⟨2501765, by rfl⟩ : syracuseStep 3335687 = 5003531) B5003531
theorem B1107679 : Blo 984595 1107679 := bstep (se 1 (by rfl) ⟨830759, by rfl⟩ : syracuseStep 1107679 = 1661519) B1661519
theorem B166127333 : Blo 984595 166127333 := bstep (se 4 (by rfl) ⟨15574437, by rfl⟩ : syracuseStep 166127333 = 31148875) B31148875
theorem B2221865 : Blo 984595 2221865 := bstep (se 2 (by rfl) ⟨833199, by rfl⟩ : syracuseStep 2221865 = 1666399) B1666399
theorem B1664975 : Blo 984595 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B16017587 : Blo 984595 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B1108255 : Blo 984595 1108255 := bstep (se 1 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 1108255 = 1662383) B1662383
theorem B11397505 : Blo 984595 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B1108543 : Blo 984595 1108543 := bstep (se 1 (by rfl) ⟨831407, by rfl⟩ : syracuseStep 1108543 = 1662815) B1662815
theorem B1665643 : Blo 984595 1665643 := bstep (se 1 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 1665643 = 2498465) B2498465
theorem B4221629 : Blo 984595 4221629 := bstep (se 3 (by rfl) ⟨791555, by rfl⟩ : syracuseStep 4221629 = 1583111) B1583111
theorem B2222927 : Blo 984595 2222927 := bstep (se 1 (by rfl) ⟨1667195, by rfl⟩ : syracuseStep 2222927 = 3334391) B3334391
theorem B1665947 : Blo 984595 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B2223143 : Blo 984595 2223143 := bstep (se 1 (by rfl) ⟨1667357, by rfl⟩ : syracuseStep 2223143 = 3334715) B3334715
theorem B2223323 : Blo 984595 2223323 := bstep (se 1 (by rfl) ⟨1667492, by rfl⟩ : syracuseStep 2223323 = 3334985) B3334985
theorem B1109371 : Blo 984595 1109371 := bstep (se 1 (by rfl) ⟨832028, by rfl⟩ : syracuseStep 1109371 = 1664057) B1664057
theorem B2223521 : Blo 984595 2223521 := bstep (se 2 (by rfl) ⟨833820, by rfl⟩ : syracuseStep 2223521 = 1667641) B1667641
theorem B40431035 : Blo 984595 40431035 := bstep (se 1 (by rfl) ⟨30323276, by rfl⟩ : syracuseStep 40431035 = 60646553) B60646553
theorem B4746833 : Blo 984595 4746833 := bstep (se 2 (by rfl) ⟨1780062, by rfl⟩ : syracuseStep 4746833 = 3560125) B3560125
theorem B21327533 : Blo 984595 21327533 := bstep (se 3 (by rfl) ⟨3998912, by rfl⟩ : syracuseStep 21327533 = 7997825) B7997825
theorem B6319883 : Blo 984595 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B1109839 : Blo 984595 1109839 := bstep (se 1 (by rfl) ⟨832379, by rfl⟩ : syracuseStep 1109839 = 1664759) B1664759
theorem B2224079 : Blo 984595 2224079 := bstep (se 1 (by rfl) ⟨1668059, by rfl⟩ : syracuseStep 2224079 = 3336119) B3336119
theorem B1110235 : Blo 984595 1110235 := bstep (se 1 (by rfl) ⟨832676, by rfl⟩ : syracuseStep 1110235 = 1665353) B1665353
theorem B1405193 : Blo 984595 1405193 := bstep (se 2 (by rfl) ⟨526947, by rfl⟩ : syracuseStep 1405193 = 1053895) B1053895
theorem B10678643 : Blo 984595 10678643 := bstep (se 1 (by rfl) ⟨8008982, by rfl⟩ : syracuseStep 10678643 = 16017965) B16017965
theorem B73855469 : Blo 984595 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B1110523 : Blo 984595 1110523 := bstep (se 1 (by rfl) ⟨832892, by rfl⟩ : syracuseStep 1110523 = 1665785) B1665785
theorem B5698201 : Blo 984595 5698201 := bstep (se 2 (by rfl) ⟨2136825, by rfl⟩ : syracuseStep 5698201 = 4273651) B4273651
theorem B1405615 : Blo 984595 1405615 := bstep (se 1 (by rfl) ⟨1054211, by rfl⟩ : syracuseStep 1405615 = 2108423) B2108423
theorem B1110703 : Blo 984595 1110703 := bstep (se 1 (by rfl) ⟨833027, by rfl⟩ : syracuseStep 1110703 = 1666055) B1666055
theorem B1110991 : Blo 984595 1110991 := bstep (se 1 (by rfl) ⟨833243, by rfl⟩ : syracuseStep 1110991 = 1666487) B1666487
theorem B1111387 : Blo 984595 1111387 := bstep (se 1 (by rfl) ⟨833540, by rfl⟩ : syracuseStep 1111387 = 1667081) B1667081
theorem B1111495 : Blo 984595 1111495 := bstep (se 1 (by rfl) ⟨833621, by rfl⟩ : syracuseStep 1111495 = 1667243) B1667243
theorem B1111855 : Blo 984595 1111855 := bstep (se 1 (by rfl) ⟨833891, by rfl⟩ : syracuseStep 1111855 = 1667783) B1667783
theorem B1111963 : Blo 984595 1111963 := bstep (se 1 (by rfl) ⟨833972, by rfl⟩ : syracuseStep 1111963 = 1667945) B1667945
theorem B4749293 : Blo 984595 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B18938123 : Blo 984595 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B4750103 : Blo 984595 4750103 := bstep (se 1 (by rfl) ⟨3562577, by rfl⟩ : syracuseStep 4750103 = 7125155) B7125155
theorem B5995451 : Blo 984595 5995451 := bstep (se 1 (by rfl) ⟨4496588, by rfl⟩ : syracuseStep 5995451 = 8993177) B8993177
theorem B1604827 : Blo 984595 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B20217077 : Blo 984595 20217077 := bstep (se 5 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 20217077 = 1895351) B1895351
theorem B7503353 : Blo 984595 7503353 := bstep (se 2 (by rfl) ⟨2813757, by rfl⟩ : syracuseStep 7503353 = 5627515) B5627515
theorem B3997487 : Blo 984595 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B6586219 : Blo 984595 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B5997007 : Blo 984595 5997007 := bstep (se 1 (by rfl) ⟨4497755, by rfl⟩ : syracuseStep 5997007 = 8995511) B8995511
theorem B43254577 : Blo 984595 43254577 := bstep (se 2 (by rfl) ⟨16220466, by rfl⟩ : syracuseStep 43254577 = 32440933) B32440933
theorem B5998175 : Blo 984595 5998175 := bstep (se 1 (by rfl) ⟨4498631, by rfl⟩ : syracuseStep 5998175 = 8997263) B8997263
theorem B984687 : Blo 984595 984687 := bstep (se 1 (by rfl) ⟨738515, by rfl⟩ : syracuseStep 984687 = 1477031) B1477031
theorem B984743 : Blo 984595 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B984827 : Blo 984595 984827 := bstep (se 1 (by rfl) ⟨738620, by rfl⟩ : syracuseStep 984827 = 1477241) B1477241
theorem B984863 : Blo 984595 984863 := bstep (se 1 (by rfl) ⟨738647, by rfl⟩ : syracuseStep 984863 = 1477295) B1477295
theorem B984895 : Blo 984595 984895 := bstep (se 1 (by rfl) ⟨738671, by rfl⟩ : syracuseStep 984895 = 1477343) B1477343
theorem B985071 : Blo 984595 985071 := bstep (se 1 (by rfl) ⟨738803, by rfl⟩ : syracuseStep 985071 = 1477607) B1477607
theorem B985243 : Blo 984595 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B985279 : Blo 984595 985279 := bstep (se 1 (by rfl) ⟨738959, by rfl⟩ : syracuseStep 985279 = 1477919) B1477919
theorem B1476905 : Blo 984595 1476905 := bstep (se 2 (by rfl) ⟨553839, by rfl⟩ : syracuseStep 1476905 = 1107679) B1107679
theorem B1476911 : Blo 984595 1476911 := bstep (se 1 (by rfl) ⟨1107683, by rfl⟩ : syracuseStep 1476911 = 2215367) B2215367
theorem B985391 : Blo 984595 985391 := bstep (se 1 (by rfl) ⟨739043, by rfl⟩ : syracuseStep 985391 = 1478087) B1478087
theorem B985627 : Blo 984595 985627 := bstep (se 1 (by rfl) ⟨739220, by rfl⟩ : syracuseStep 985627 = 1478441) B1478441
theorem B1477151 : Blo 984595 1477151 := bstep (se 1 (by rfl) ⟨1107863, by rfl⟩ : syracuseStep 1477151 = 2215727) B2215727
theorem B985631 : Blo 984595 985631 := bstep (se 1 (by rfl) ⟨739223, by rfl⟩ : syracuseStep 985631 = 1478447) B1478447
theorem B1870523 : Blo 984595 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B985947 : Blo 984595 985947 := bstep (se 1 (by rfl) ⟨739460, by rfl⟩ : syracuseStep 985947 = 1478921) B1478921
theorem B1477535 : Blo 984595 1477535 := bstep (se 1 (by rfl) ⟨1108151, by rfl⟩ : syracuseStep 1477535 = 2216303) B2216303
theorem B986015 : Blo 984595 986015 := bstep (se 1 (by rfl) ⟨739511, by rfl⟩ : syracuseStep 986015 = 1479023) B1479023
theorem B1477583 : Blo 984595 1477583 := bstep (se 1 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 1477583 = 2216375) B2216375
theorem B1477673 : Blo 984595 1477673 := bstep (se 2 (by rfl) ⟨554127, by rfl⟩ : syracuseStep 1477673 = 1108255) B1108255
theorem B1477679 : Blo 984595 1477679 := bstep (se 1 (by rfl) ⟨1108259, by rfl⟩ : syracuseStep 1477679 = 2216519) B2216519
theorem B986159 : Blo 984595 986159 := bstep (se 1 (by rfl) ⟨739619, by rfl⟩ : syracuseStep 986159 = 1479239) B1479239
theorem B1477703 : Blo 984595 1477703 := bstep (se 1 (by rfl) ⟨1108277, by rfl⟩ : syracuseStep 1477703 = 2216555) B2216555
theorem B986183 : Blo 984595 986183 := bstep (se 1 (by rfl) ⟨739637, by rfl⟩ : syracuseStep 986183 = 1479275) B1479275
theorem B986335 : Blo 984595 986335 := bstep (se 1 (by rfl) ⟨739751, by rfl⟩ : syracuseStep 986335 = 1479503) B1479503
theorem B3738905 : Blo 984595 3738905 := bstep (se 2 (by rfl) ⟨1402089, by rfl⟩ : syracuseStep 3738905 = 2804179) B2804179
theorem B1477967 : Blo 984595 1477967 := bstep (se 1 (by rfl) ⟨1108475, by rfl⟩ : syracuseStep 1477967 = 2216951) B2216951
theorem B1478057 : Blo 984595 1478057 := bstep (se 2 (by rfl) ⟨554271, by rfl⟩ : syracuseStep 1478057 = 1108543) B1108543
theorem B986599 : Blo 984595 986599 := bstep (se 1 (by rfl) ⟨739949, by rfl⟩ : syracuseStep 986599 = 1479899) B1479899
theorem B9014777 : Blo 984595 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1478207 : Blo 984595 1478207 := bstep (se 1 (by rfl) ⟨1108655, by rfl⟩ : syracuseStep 1478207 = 2217311) B2217311
theorem B986715 : Blo 984595 986715 := bstep (se 1 (by rfl) ⟨740036, by rfl⟩ : syracuseStep 986715 = 1480073) B1480073
theorem B6327983 : Blo 984595 6327983 := bstep (se 1 (by rfl) ⟨4745987, by rfl⟩ : syracuseStep 6327983 = 9491975) B9491975
theorem B1478471 : Blo 984595 1478471 := bstep (se 1 (by rfl) ⟨1108853, by rfl⟩ : syracuseStep 1478471 = 2217707) B2217707
theorem B986951 : Blo 984595 986951 := bstep (se 1 (by rfl) ⟨740213, by rfl⟩ : syracuseStep 986951 = 1480427) B1480427
theorem B1478555 : Blo 984595 1478555 := bstep (se 1 (by rfl) ⟨1108916, by rfl⟩ : syracuseStep 1478555 = 2217833) B2217833
theorem B987103 : Blo 984595 987103 := bstep (se 1 (by rfl) ⟨740327, by rfl⟩ : syracuseStep 987103 = 1480655) B1480655
theorem B987367 : Blo 984595 987367 := bstep (se 1 (by rfl) ⟨740525, by rfl⟩ : syracuseStep 987367 = 1481051) B1481051
theorem B1249663 : Blo 984595 1249663 := bstep (se 1 (by rfl) ⟨937247, by rfl⟩ : syracuseStep 1249663 = 1874495) B1874495
theorem B987519 : Blo 984595 987519 := bstep (se 1 (by rfl) ⟨740639, by rfl⟩ : syracuseStep 987519 = 1481279) B1481279
theorem B1479119 : Blo 984595 1479119 := bstep (se 1 (by rfl) ⟨1109339, by rfl⟩ : syracuseStep 1479119 = 2218679) B2218679
theorem B987599 : Blo 984595 987599 := bstep (se 1 (by rfl) ⟨740699, by rfl⟩ : syracuseStep 987599 = 1481399) B1481399
theorem B1479161 : Blo 984595 1479161 := bstep (se 2 (by rfl) ⟨554685, by rfl⟩ : syracuseStep 1479161 = 1109371) B1109371
theorem B1872467 : Blo 984595 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B1479263 : Blo 984595 1479263 := bstep (se 1 (by rfl) ⟨1109447, by rfl⟩ : syracuseStep 1479263 = 2218895) B2218895
theorem B987751 : Blo 984595 987751 := bstep (se 1 (by rfl) ⟨740813, by rfl⟩ : syracuseStep 987751 = 1481627) B1481627
theorem B988015 : Blo 984595 988015 := bstep (se 1 (by rfl) ⟨741011, by rfl⟩ : syracuseStep 988015 = 1482023) B1482023
theorem B8426375 : Blo 984595 8426375 := bstep (se 1 (by rfl) ⟨6319781, by rfl⟩ : syracuseStep 8426375 = 12639563) B12639563
theorem B988071 : Blo 984595 988071 := bstep (se 1 (by rfl) ⟨741053, by rfl⟩ : syracuseStep 988071 = 1482107) B1482107
theorem B988155 : Blo 984595 988155 := bstep (se 1 (by rfl) ⟨741116, by rfl⟩ : syracuseStep 988155 = 1482233) B1482233
theorem B3740681 : Blo 984595 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B4002871 : Blo 984595 4002871 := bstep (se 1 (by rfl) ⟨3002153, by rfl⟩ : syracuseStep 4002871 = 6004307) B6004307
theorem B1479743 : Blo 984595 1479743 := bstep (se 1 (by rfl) ⟨1109807, by rfl⟩ : syracuseStep 1479743 = 2219615) B2219615
theorem B988223 : Blo 984595 988223 := bstep (se 1 (by rfl) ⟨741167, by rfl⟩ : syracuseStep 988223 = 1482335) B1482335
theorem B5477483 : Blo 984595 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B1479785 : Blo 984595 1479785 := bstep (se 2 (by rfl) ⟨554919, by rfl⟩ : syracuseStep 1479785 = 1109839) B1109839
theorem B1479887 : Blo 984595 1479887 := bstep (se 1 (by rfl) ⟨1109915, by rfl⟩ : syracuseStep 1479887 = 2219831) B2219831
theorem B988367 : Blo 984595 988367 := bstep (se 1 (by rfl) ⟨741275, by rfl⟩ : syracuseStep 988367 = 1482551) B1482551
theorem B1774867 : Blo 984595 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B1480091 : Blo 984595 1480091 := bstep (se 1 (by rfl) ⟨1110068, by rfl⟩ : syracuseStep 1480091 = 2220137) B2220137
theorem B988571 : Blo 984595 988571 := bstep (se 1 (by rfl) ⟨741428, by rfl⟩ : syracuseStep 988571 = 1482857) B1482857
theorem B1480313 : Blo 984595 1480313 := bstep (se 2 (by rfl) ⟨555117, by rfl⟩ : syracuseStep 1480313 = 1110235) B1110235
theorem B1480415 : Blo 984595 1480415 := bstep (se 1 (by rfl) ⟨1110311, by rfl⟩ : syracuseStep 1480415 = 2220623) B2220623
theorem B1054459 : Blo 984595 1054459 := bstep (se 1 (by rfl) ⟨790844, by rfl⟩ : syracuseStep 1054459 = 1581689) B1581689
theorem B1480511 : Blo 984595 1480511 := bstep (se 1 (by rfl) ⟨1110383, by rfl⟩ : syracuseStep 1480511 = 2220767) B2220767
theorem B1578889 : Blo 984595 1578889 := bstep (se 2 (by rfl) ⟨592083, by rfl⟩ : syracuseStep 1578889 = 1184167) B1184167
theorem B1480679 : Blo 984595 1480679 := bstep (se 1 (by rfl) ⟨1110509, by rfl⟩ : syracuseStep 1480679 = 2221019) B2221019
theorem B1480697 : Blo 984595 1480697 := bstep (se 2 (by rfl) ⟨555261, by rfl⟩ : syracuseStep 1480697 = 1110523) B1110523
theorem B1480799 : Blo 984595 1480799 := bstep (se 1 (by rfl) ⟨1110599, by rfl⟩ : syracuseStep 1480799 = 2221199) B2221199
theorem B1480859 : Blo 984595 1480859 := bstep (se 1 (by rfl) ⟨1110644, by rfl⟩ : syracuseStep 1480859 = 2221289) B2221289
theorem B1480895 : Blo 984595 1480895 := bstep (se 1 (by rfl) ⟨1110671, by rfl⟩ : syracuseStep 1480895 = 2221343) B2221343
theorem B1874153 : Blo 984595 1874153 := bstep (se 2 (by rfl) ⟨702807, by rfl⟩ : syracuseStep 1874153 = 1405615) B1405615
theorem B1480937 : Blo 984595 1480937 := bstep (se 2 (by rfl) ⟨555351, by rfl⟩ : syracuseStep 1480937 = 1110703) B1110703
theorem B1775911 : Blo 984595 1775911 := bstep (se 1 (by rfl) ⟨1331933, by rfl⟩ : syracuseStep 1775911 = 2663867) B2663867
theorem B1481243 : Blo 984595 1481243 := bstep (se 1 (by rfl) ⟨1110932, by rfl⟩ : syracuseStep 1481243 = 2221865) B2221865
theorem B1481321 : Blo 984595 1481321 := bstep (se 2 (by rfl) ⟨555495, by rfl⟩ : syracuseStep 1481321 = 1110991) B1110991
theorem B1186651 : Blo 984595 1186651 := bstep (se 1 (by rfl) ⟨889988, by rfl⟩ : syracuseStep 1186651 = 1779977) B1779977
theorem B1186795 : Blo 984595 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B1481849 : Blo 984595 1481849 := bstep (se 2 (by rfl) ⟨555693, by rfl⟩ : syracuseStep 1481849 = 1111387) B1111387
theorem B4005011 : Blo 984595 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B1481951 : Blo 984595 1481951 := bstep (se 1 (by rfl) ⟨1111463, by rfl⟩ : syracuseStep 1481951 = 2222927) B2222927
theorem B6397181 : Blo 984595 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B1481993 : Blo 984595 1481993 := bstep (se 2 (by rfl) ⟨555747, by rfl⟩ : syracuseStep 1481993 = 1111495) B1111495
theorem B1482095 : Blo 984595 1482095 := bstep (se 1 (by rfl) ⟨1111571, by rfl⟩ : syracuseStep 1482095 = 2223143) B2223143
theorem B1482215 : Blo 984595 1482215 := bstep (se 1 (by rfl) ⟨1111661, by rfl⟩ : syracuseStep 1482215 = 2223323) B2223323
theorem B1580651 : Blo 984595 1580651 := bstep (se 1 (by rfl) ⟨1185488, by rfl⟩ : syracuseStep 1580651 = 2370977) B2370977
theorem B1482347 : Blo 984595 1482347 := bstep (se 1 (by rfl) ⟨1111760, by rfl⟩ : syracuseStep 1482347 = 2223521) B2223521
theorem B2498273 : Blo 984595 2498273 := bstep (se 2 (by rfl) ⟨936852, by rfl⟩ : syracuseStep 2498273 = 1873705) B1873705
theorem B1482473 : Blo 984595 1482473 := bstep (se 2 (by rfl) ⟨555927, by rfl⟩ : syracuseStep 1482473 = 1111855) B1111855
theorem B1482617 : Blo 984595 1482617 := bstep (se 2 (by rfl) ⟨555981, by rfl⟩ : syracuseStep 1482617 = 1111963) B1111963
theorem B1580971 : Blo 984595 1580971 := bstep (se 1 (by rfl) ⟨1185728, by rfl⟩ : syracuseStep 1580971 = 2371457) B2371457
theorem B1482719 : Blo 984595 1482719 := bstep (se 1 (by rfl) ⟨1112039, by rfl⟩ : syracuseStep 1482719 = 2224079) B2224079
theorem B7119095 : Blo 984595 7119095 := bstep (se 1 (by rfl) ⟨5339321, by rfl⟩ : syracuseStep 7119095 = 10678643) B10678643
theorem B1778441 : Blo 984595 1778441 := bstep (se 2 (by rfl) ⟨666915, by rfl⟩ : syracuseStep 1778441 = 1333831) B1333831
theorem B3744569 : Blo 984595 3744569 := bstep (se 2 (by rfl) ⟨1404213, by rfl⟩ : syracuseStep 3744569 = 2808427) B2808427
theorem B107816093 : Blo 984595 107816093 := bstep (se 3 (by rfl) ⟨20215517, by rfl⟩ : syracuseStep 107816093 = 40431035) B40431035
theorem B8430749 : Blo 984595 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B2106731 : Blo 984595 2106731 := bstep (se 1 (by rfl) ⟨1580048, by rfl⟩ : syracuseStep 2106731 = 3160097) B3160097
theorem B12625415 : Blo 984595 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B2500217 : Blo 984595 2500217 := bstep (se 2 (by rfl) ⟨937581, by rfl⟩ : syracuseStep 2500217 = 1875163) B1875163
theorem B2139769 : Blo 984595 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B16853021 : Blo 984595 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B13478051 : Blo 984595 13478051 := bstep (se 1 (by rfl) ⟨10108538, by rfl⟩ : syracuseStep 13478051 = 20217077) B20217077
theorem B3746209 : Blo 984595 3746209 := bstep (se 2 (by rfl) ⟨1404828, by rfl⟩ : syracuseStep 3746209 = 2809657) B2809657
theorem B2664991 : Blo 984595 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B83143361 : Blo 984595 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B3550007 : Blo 984595 3550007 := bstep (se 1 (by rfl) ⟨2662505, by rfl⟩ : syracuseStep 3550007 = 5325011) B5325011
theorem B28454237 : Blo 984595 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B3747181 : Blo 984595 3747181 := bstep (se 3 (by rfl) ⟨702596, by rfl⟩ : syracuseStep 3747181 = 1405193) B1405193
theorem B3550783 : Blo 984595 3550783 := bstep (se 1 (by rfl) ⟨2663087, by rfl⟩ : syracuseStep 3550783 = 5326175) B5326175
theorem B42675821 : Blo 984595 42675821 := bstep (se 3 (by rfl) ⟨8001716, by rfl⟩ : syracuseStep 42675821 = 16003433) B16003433
theorem B4206491 : Blo 984595 4206491 := bstep (se 1 (by rfl) ⟨3154868, by rfl⟩ : syracuseStep 4206491 = 6309737) B6309737
theorem B12660785 : Blo 984595 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B4272527 : Blo 984595 4272527 := bstep (se 1 (by rfl) ⟨3204395, by rfl⟩ : syracuseStep 4272527 = 6408791) B6408791
theorem B8434439 : Blo 984595 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B4994459 : Blo 984595 4994459 := bstep (se 1 (by rfl) ⟨3745844, by rfl⟩ : syracuseStep 4994459 = 7491689) B7491689
theorem B6763931 : Blo 984595 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B3159623 : Blo 984595 3159623 := bstep (se 1 (by rfl) ⟨2369717, by rfl⟩ : syracuseStep 3159623 = 4739435) B4739435
theorem B5617309 : Blo 984595 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B3749611 : Blo 984595 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B3160147 : Blo 984595 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B2373715 : Blo 984595 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B5617835 : Blo 984595 5617835 := bstep (se 1 (by rfl) ⟨4213376, by rfl⟩ : syracuseStep 5617835 = 8426753) B8426753
theorem B110803715 : Blo 984595 110803715 := bstep (se 1 (by rfl) ⟨83102786, by rfl⟩ : syracuseStep 110803715 = 166205573) B166205573
theorem B2997071 : Blo 984595 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B443006221 : Blo 984595 443006221 := bstep (se 3 (by rfl) ⟨83063666, by rfl⟩ : syracuseStep 443006221 = 166127333) B166127333
theorem B5619041 : Blo 984595 5619041 := bstep (se 2 (by rfl) ⟨2107140, by rfl⟩ : syracuseStep 5619041 = 4214281) B4214281
theorem B9617129 : Blo 984595 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B3325751 : Blo 984595 3325751 := bstep (se 1 (by rfl) ⟨2494313, by rfl⟩ : syracuseStep 3325751 = 4988627) B4988627
theorem B3555197 : Blo 984595 3555197 := bstep (se 3 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 3555197 = 1333199) B1333199
theorem B12664781 : Blo 984595 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B3326183 : Blo 984595 3326183 := bstep (se 1 (by rfl) ⟨2494637, by rfl⟩ : syracuseStep 3326183 = 4989275) B4989275
theorem B8667575 : Blo 984595 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B11977379 : Blo 984595 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B3326777 : Blo 984595 3326777 := bstep (se 2 (by rfl) ⟨1247541, by rfl⟩ : syracuseStep 3326777 = 2495083) B2495083
theorem B3326831 : Blo 984595 3326831 := bstep (se 1 (by rfl) ⟨2495123, by rfl⟩ : syracuseStep 3326831 = 4990247) B4990247
theorem B12633205 : Blo 984595 12633205 := bstep (se 5 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 12633205 = 1184363) B1184363
theorem B10142941 : Blo 984595 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B3327641 : Blo 984595 3327641 := bstep (se 2 (by rfl) ⟨1247865, by rfl⟩ : syracuseStep 3327641 = 2495731) B2495731
theorem B1689833 : Blo 984595 1689833 := bstep (se 2 (by rfl) ⟨633687, by rfl⟩ : syracuseStep 1689833 = 1267375) B1267375
theorem B3328235 : Blo 984595 3328235 := bstep (se 1 (by rfl) ⟨2496176, by rfl⟩ : syracuseStep 3328235 = 4992353) B4992353
theorem B3164555 : Blo 984595 3164555 := bstep (se 1 (by rfl) ⟨2373416, by rfl⟩ : syracuseStep 3164555 = 4746833) B4746833
theorem B4737437 : Blo 984595 4737437 := bstep (se 3 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 4737437 = 1776539) B1776539
theorem B5622209 : Blo 984595 5622209 := bstep (se 2 (by rfl) ⟨2108328, by rfl⟩ : syracuseStep 5622209 = 4216657) B4216657
theorem B2804395 : Blo 984595 2804395 := bstep (se 1 (by rfl) ⟨2103296, by rfl⟩ : syracuseStep 2804395 = 4206593) B4206593
theorem B7588703 : Blo 984595 7588703 := bstep (se 1 (by rfl) ⟨5691527, by rfl⟩ : syracuseStep 7588703 = 11383055) B11383055
theorem B4737953 : Blo 984595 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B49236979 : Blo 984595 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B3329531 : Blo 984595 3329531 := bstep (se 1 (by rfl) ⟨2497148, by rfl⟩ : syracuseStep 3329531 = 4994297) B4994297
theorem B3329693 : Blo 984595 3329693 := bstep (se 3 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 3329693 = 1248635) B1248635
theorem B2215835 : Blo 984595 2215835 := bstep (se 1 (by rfl) ⟨1661876, by rfl⟩ : syracuseStep 2215835 = 3323753) B3323753
theorem B11980781 : Blo 984595 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B3330233 : Blo 984595 3330233 := bstep (se 2 (by rfl) ⟨1248837, by rfl⟩ : syracuseStep 3330233 = 2497675) B2497675
theorem B2216123 : Blo 984595 2216123 := bstep (se 1 (by rfl) ⟨1662092, by rfl⟩ : syracuseStep 2216123 = 3324185) B3324185
theorem B2806127 : Blo 984595 2806127 := bstep (se 1 (by rfl) ⟨2104595, by rfl⟩ : syracuseStep 2806127 = 4209191) B4209191
theorem B7098797 : Blo 984595 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B3166735 : Blo 984595 3166735 := bstep (se 1 (by rfl) ⟨2375051, by rfl⟩ : syracuseStep 3166735 = 4750103) B4750103
theorem B2216609 : Blo 984595 2216609 := bstep (se 2 (by rfl) ⟨831228, by rfl⟩ : syracuseStep 2216609 = 1662457) B1662457
theorem B5624599 : Blo 984595 5624599 := bstep (se 1 (by rfl) ⟨4218449, by rfl⟩ : syracuseStep 5624599 = 8436899) B8436899
theorem B5002235 : Blo 984595 5002235 := bstep (se 1 (by rfl) ⟨3751676, by rfl⟩ : syracuseStep 5002235 = 7503353) B7503353
theorem B2216969 : Blo 984595 2216969 := bstep (se 2 (by rfl) ⟨831363, by rfl⟩ : syracuseStep 2216969 = 1662727) B1662727
theorem B2217023 : Blo 984595 2217023 := bstep (se 1 (by rfl) ⟨1662767, by rfl⟩ : syracuseStep 2217023 = 3325535) B3325535
theorem B3200411 : Blo 984595 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B5002721 : Blo 984595 5002721 := bstep (se 2 (by rfl) ⟨1876020, by rfl⟩ : syracuseStep 5002721 = 3752041) B3752041
theorem B1463879 : Blo 984595 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B13522555 : Blo 984595 13522555 := bstep (se 1 (by rfl) ⟨10141916, by rfl⟩ : syracuseStep 13522555 = 20283833) B20283833
theorem B2217959 : Blo 984595 2217959 := bstep (se 1 (by rfl) ⟨1663469, by rfl⟩ : syracuseStep 2217959 = 3326939) B3326939
theorem B2217977 : Blo 984595 2217977 := bstep (se 2 (by rfl) ⟨831741, by rfl⟩ : syracuseStep 2217977 = 1663483) B1663483
theorem B7493633 : Blo 984595 7493633 := bstep (se 2 (by rfl) ⟨2810112, by rfl⟩ : syracuseStep 7493633 = 5620225) B5620225
theorem B2218067 : Blo 984595 2218067 := bstep (se 1 (by rfl) ⟨1663550, by rfl⟩ : syracuseStep 2218067 = 3327101) B3327101
theorem B3561569 : Blo 984595 3561569 := bstep (se 2 (by rfl) ⟨1335588, by rfl⟩ : syracuseStep 3561569 = 2671177) B2671177
theorem B2218139 : Blo 984595 2218139 := bstep (se 1 (by rfl) ⟨1663604, by rfl⟩ : syracuseStep 2218139 = 3327209) B3327209
theorem B3332339 : Blo 984595 3332339 := bstep (se 1 (by rfl) ⟨2499254, by rfl⟩ : syracuseStep 3332339 = 4998509) B4998509
theorem B2218247 : Blo 984595 2218247 := bstep (se 1 (by rfl) ⟨1663685, by rfl⟩ : syracuseStep 2218247 = 3327371) B3327371
theorem B12146959 : Blo 984595 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B3332393 : Blo 984595 3332393 := bstep (se 2 (by rfl) ⟨1249647, by rfl⟩ : syracuseStep 3332393 = 2499295) B2499295
theorem B3561769 : Blo 984595 3561769 := bstep (se 2 (by rfl) ⟨1335663, by rfl⟩ : syracuseStep 3561769 = 2671327) B2671327
theorem B5626331 : Blo 984595 5626331 := bstep (se 1 (by rfl) ⟨4219748, by rfl⟩ : syracuseStep 5626331 = 8439497) B8439497
theorem B2218553 : Blo 984595 2218553 := bstep (se 2 (by rfl) ⟨831957, by rfl⟩ : syracuseStep 2218553 = 1663915) B1663915
theorem B1661627 : Blo 984595 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B6740779 : Blo 984595 6740779 := bstep (se 1 (by rfl) ⟨5055584, by rfl⟩ : syracuseStep 6740779 = 10111169) B10111169
theorem B6314861 : Blo 984595 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B8444897 : Blo 984595 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B5004503 : Blo 984595 5004503 := bstep (se 1 (by rfl) ⟨3753377, by rfl⟩ : syracuseStep 5004503 = 7506755) B7506755
theorem B2219273 : Blo 984595 2219273 := bstep (se 2 (by rfl) ⟨832227, by rfl⟩ : syracuseStep 2219273 = 1664455) B1664455
theorem B7101857 : Blo 984595 7101857 := bstep (se 2 (by rfl) ⟨2663196, by rfl⟩ : syracuseStep 7101857 = 5326393) B5326393
theorem B5332385 : Blo 984595 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B1334875 : Blo 984595 1334875 := bstep (se 1 (by rfl) ⟨1001156, by rfl⟩ : syracuseStep 1334875 = 2002313) B2002313
theorem B3333959 : Blo 984595 3333959 := bstep (se 1 (by rfl) ⟨2500469, by rfl⟩ : syracuseStep 3333959 = 5000939) B5000939
theorem B3334013 : Blo 984595 3334013 := bstep (se 3 (by rfl) ⟨625127, by rfl⟩ : syracuseStep 3334013 = 1250255) B1250255
theorem B6315965 : Blo 984595 6315965 := bstep (se 3 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 6315965 = 2368487) B2368487
theorem B1662943 : Blo 984595 1662943 := bstep (se 1 (by rfl) ⟨1247207, by rfl⟩ : syracuseStep 1662943 = 2494415) B2494415
theorem B3334283 : Blo 984595 3334283 := bstep (se 1 (by rfl) ⟨2500712, by rfl⟩ : syracuseStep 3334283 = 5001425) B5001425
theorem B2220263 : Blo 984595 2220263 := bstep (se 1 (by rfl) ⟨1665197, by rfl⟩ : syracuseStep 2220263 = 3330395) B3330395
theorem B9593275 : Blo 984595 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B3334607 : Blo 984595 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B15196673 : Blo 984595 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B1663591 : Blo 984595 1663591 := bstep (se 1 (by rfl) ⟨1247693, by rfl⟩ : syracuseStep 1663591 = 2495387) B2495387
theorem B21652103 : Blo 984595 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B1663753 : Blo 984595 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B3334931 : Blo 984595 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B2220857 : Blo 984595 2220857 := bstep (se 2 (by rfl) ⟨832821, by rfl⟩ : syracuseStep 2220857 = 1665643) B1665643
theorem B2220911 : Blo 984595 2220911 := bstep (se 1 (by rfl) ⟨1665683, by rfl⟩ : syracuseStep 2220911 = 3331367) B3331367
theorem B1139707 : Blo 984595 1139707 := bstep (se 1 (by rfl) ⟨854780, by rfl⟩ : syracuseStep 1139707 = 1709561) B1709561
theorem B1664347 : Blo 984595 1664347 := bstep (se 1 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 1664347 = 2496521) B2496521
theorem B2221487 : Blo 984595 2221487 := bstep (se 1 (by rfl) ⟨1666115, by rfl⟩ : syracuseStep 2221487 = 3332231) B3332231
theorem B6743567 : Blo 984595 6743567 := bstep (se 1 (by rfl) ⟨5057675, by rfl⟩ : syracuseStep 6743567 = 10115351) B10115351
theorem B5629499 : Blo 984595 5629499 := bstep (se 1 (by rfl) ⟨4222124, by rfl⟩ : syracuseStep 5629499 = 8444249) B8444249
theorem B2811503 : Blo 984595 2811503 := bstep (se 1 (by rfl) ⟨2108627, by rfl⟩ : syracuseStep 2811503 = 4217255) B4217255
theorem B3335795 : Blo 984595 3335795 := bstep (se 1 (by rfl) ⟨2501846, by rfl⟩ : syracuseStep 3335795 = 5003693) B5003693
theorem B13493927 : Blo 984595 13493927 := bstep (se 1 (by rfl) ⟨10120445, by rfl⟩ : syracuseStep 13493927 = 20240891) B20240891
theorem B1402591 : Blo 984595 1402591 := bstep (se 1 (by rfl) ⟨1051943, by rfl⟩ : syracuseStep 1402591 = 2103887) B2103887
theorem B3335903 : Blo 984595 3335903 := bstep (se 1 (by rfl) ⟨2501927, by rfl⟩ : syracuseStep 3335903 = 5003855) B5003855
theorem B1402687 : Blo 984595 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B3336065 : Blo 984595 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B2222315 : Blo 984595 2222315 := bstep (se 1 (by rfl) ⟨1666736, by rfl⟩ : syracuseStep 2222315 = 3333473) B3333473
theorem B7498007 : Blo 984595 7498007 := bstep (se 1 (by rfl) ⟨5623505, by rfl⟩ : syracuseStep 7498007 = 11247011) B11247011
theorem B1665319 : Blo 984595 1665319 := bstep (se 1 (by rfl) ⟨1248989, by rfl⟩ : syracuseStep 1665319 = 2497979) B2497979
theorem B1403183 : Blo 984595 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B6318425 : Blo 984595 6318425 := bstep (se 2 (by rfl) ⟨2369409, by rfl⟩ : syracuseStep 6318425 = 4738819) B4738819
theorem B281373101 : Blo 984595 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B1108507 : Blo 984595 1108507 := bstep (se 1 (by rfl) ⟨831380, by rfl⟩ : syracuseStep 1108507 = 1662761) B1662761
theorem B4745911 : Blo 984595 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B3992555 : Blo 984595 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B1666271 : Blo 984595 1666271 := bstep (se 1 (by rfl) ⟨1249703, by rfl⟩ : syracuseStep 1666271 = 2499407) B2499407
theorem B13495567 : Blo 984595 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B1109479 : Blo 984595 1109479 := bstep (se 1 (by rfl) ⟨832109, by rfl⟩ : syracuseStep 1109479 = 1664219) B1664219
theorem B2223611 : Blo 984595 2223611 := bstep (se 1 (by rfl) ⟨1667708, by rfl⟩ : syracuseStep 2223611 = 3335417) B3335417
theorem B7597601 : Blo 984595 7597601 := bstep (se 2 (by rfl) ⟨2849100, by rfl⟩ : syracuseStep 7597601 = 5698201) B5698201
theorem B1666703 : Blo 984595 1666703 := bstep (se 1 (by rfl) ⟨1250027, by rfl⟩ : syracuseStep 1666703 = 2500055) B2500055
theorem B2223791 : Blo 984595 2223791 := bstep (se 1 (by rfl) ⟨1667843, by rfl⟩ : syracuseStep 2223791 = 3335687) B3335687
theorem B1666939 : Blo 984595 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B1109983 : Blo 984595 1109983 := bstep (se 1 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 1109983 = 1664975) B1664975
theorem B10678391 : Blo 984595 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B8417627 : Blo 984595 8417627 := bstep (se 1 (by rfl) ⟨6313220, by rfl⟩ : syracuseStep 8417627 = 12626441) B12626441
theorem B6320551 : Blo 984595 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B2814419 : Blo 984595 2814419 := bstep (se 1 (by rfl) ⟨2110814, by rfl⟩ : syracuseStep 2814419 = 4221629) B4221629
theorem B5337683 : Blo 984595 5337683 := bstep (se 1 (by rfl) ⟨4003262, by rfl⟩ : syracuseStep 5337683 = 8006525) B8006525
theorem B1110631 : Blo 984595 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B1602283 : Blo 984595 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B14218355 : Blo 984595 14218355 := bstep (se 1 (by rfl) ⟨10663766, by rfl⟩ : syracuseStep 14218355 = 21327533) B21327533
theorem B9008435 : Blo 984595 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B4749641 : Blo 984595 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B11238263 : Blo 984595 11238263 := bstep (se 1 (by rfl) ⟨8428697, by rfl⟩ : syracuseStep 11238263 = 16857395) B16857395
theorem B3996967 : Blo 984595 3996967 := bstep (se 1 (by rfl) ⟨2997725, by rfl⟩ : syracuseStep 3996967 = 5995451) B5995451
theorem B8781625 : Blo 984595 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B5341099 : Blo 984595 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B7996009 : Blo 984595 7996009 := bstep (se 2 (by rfl) ⟨2998503, by rfl⟩ : syracuseStep 7996009 = 5997007) B5997007
theorem B3998783 : Blo 984595 3998783 := bstep (se 1 (by rfl) ⟨2999087, by rfl⟩ : syracuseStep 3998783 = 5998175) B5998175
theorem B57672769 : Blo 984595 57672769 := bstep (se 2 (by rfl) ⟨21627288, by rfl⟩ : syracuseStep 57672769 = 43254577) B43254577
theorem B16844273 : Blo 984595 16844273 := bstep (se 2 (by rfl) ⟨6316602, by rfl⟩ : syracuseStep 16844273 = 12633205) B12633205
theorem B984603 : Blo 984595 984603 := bstep (se 1 (by rfl) ⟨738452, by rfl⟩ : syracuseStep 984603 = 1476905) B1476905
theorem B984607 : Blo 984595 984607 := bstep (se 1 (by rfl) ⟨738455, by rfl⟩ : syracuseStep 984607 = 1476911) B1476911
theorem B984767 : Blo 984595 984767 := bstep (se 1 (by rfl) ⟨738575, by rfl⟩ : syracuseStep 984767 = 1477151) B1477151
theorem B1247015 : Blo 984595 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B985023 : Blo 984595 985023 := bstep (se 1 (by rfl) ⟨738767, by rfl⟩ : syracuseStep 985023 = 1477535) B1477535
theorem B985055 : Blo 984595 985055 := bstep (se 1 (by rfl) ⟨738791, by rfl⟩ : syracuseStep 985055 = 1477583) B1477583
theorem B985115 : Blo 984595 985115 := bstep (se 1 (by rfl) ⟨738836, by rfl⟩ : syracuseStep 985115 = 1477673) B1477673
theorem B985119 : Blo 984595 985119 := bstep (se 1 (by rfl) ⟨738839, by rfl⟩ : syracuseStep 985119 = 1477679) B1477679
theorem B985135 : Blo 984595 985135 := bstep (se 1 (by rfl) ⟨738851, by rfl⟩ : syracuseStep 985135 = 1477703) B1477703
theorem B2853025 : Blo 984595 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B2492603 : Blo 984595 2492603 := bstep (se 1 (by rfl) ⟨1869452, by rfl⟩ : syracuseStep 2492603 = 3738905) B3738905
theorem B985311 : Blo 984595 985311 := bstep (se 1 (by rfl) ⟨738983, by rfl⟩ : syracuseStep 985311 = 1477967) B1477967
theorem B985371 : Blo 984595 985371 := bstep (se 1 (by rfl) ⟨739028, by rfl⟩ : syracuseStep 985371 = 1478057) B1478057
theorem B1870121 : Blo 984595 1870121 := bstep (se 2 (by rfl) ⟨701295, by rfl⟩ : syracuseStep 1870121 = 1402591) B1402591
theorem B985471 : Blo 984595 985471 := bstep (se 1 (by rfl) ⟨739103, by rfl⟩ : syracuseStep 985471 = 1478207) B1478207
theorem B985647 : Blo 984595 985647 := bstep (se 1 (by rfl) ⟨739235, by rfl⟩ : syracuseStep 985647 = 1478471) B1478471
theorem B1477223 : Blo 984595 1477223 := bstep (se 1 (by rfl) ⟨1107917, by rfl⟩ : syracuseStep 1477223 = 2215835) B2215835
theorem B985703 : Blo 984595 985703 := bstep (se 1 (by rfl) ⟨739277, by rfl⟩ : syracuseStep 985703 = 1478555) B1478555
theorem B1477415 : Blo 984595 1477415 := bstep (se 1 (by rfl) ⟨1108061, by rfl⟩ : syracuseStep 1477415 = 2216123) B2216123
theorem B1870751 : Blo 984595 1870751 := bstep (se 1 (by rfl) ⟨1403063, by rfl⟩ : syracuseStep 1870751 = 2806127) B2806127
theorem B986079 : Blo 984595 986079 := bstep (se 1 (by rfl) ⟨739559, by rfl⟩ : syracuseStep 986079 = 1479119) B1479119
theorem B986107 : Blo 984595 986107 := bstep (se 1 (by rfl) ⟨739580, by rfl⟩ : syracuseStep 986107 = 1479161) B1479161
theorem B1248311 : Blo 984595 1248311 := bstep (se 1 (by rfl) ⟨936233, by rfl⟩ : syracuseStep 1248311 = 1872467) B1872467
theorem B986175 : Blo 984595 986175 := bstep (se 1 (by rfl) ⟨739631, by rfl⟩ : syracuseStep 986175 = 1479263) B1479263
theorem B1477739 : Blo 984595 1477739 := bstep (se 1 (by rfl) ⟨1108304, by rfl⟩ : syracuseStep 1477739 = 2216609) B2216609
theorem B2493787 : Blo 984595 2493787 := bstep (se 1 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 2493787 = 3740681) B3740681
theorem B1477979 : Blo 984595 1477979 := bstep (se 1 (by rfl) ⟨1108484, by rfl⟩ : syracuseStep 1477979 = 2216969) B2216969
theorem B1478009 : Blo 984595 1478009 := bstep (se 2 (by rfl) ⟨554253, by rfl⟩ : syracuseStep 1478009 = 1108507) B1108507
theorem B1478015 : Blo 984595 1478015 := bstep (se 1 (by rfl) ⟨1108511, by rfl⟩ : syracuseStep 1478015 = 2217023) B2217023
theorem B986495 : Blo 984595 986495 := bstep (se 1 (by rfl) ⟨739871, by rfl⟩ : syracuseStep 986495 = 1479743) B1479743
theorem B986523 : Blo 984595 986523 := bstep (se 1 (by rfl) ⟨739892, by rfl⟩ : syracuseStep 986523 = 1479785) B1479785
theorem B986591 : Blo 984595 986591 := bstep (se 1 (by rfl) ⟨739943, by rfl⟩ : syracuseStep 986591 = 1479887) B1479887
theorem B3739193 : Blo 984595 3739193 := bstep (se 2 (by rfl) ⟨1402197, by rfl⟩ : syracuseStep 3739193 = 2804395) B2804395
theorem B6327881 : Blo 984595 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B2133607 : Blo 984595 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B986727 : Blo 984595 986727 := bstep (se 1 (by rfl) ⟨740045, by rfl⟩ : syracuseStep 986727 = 1480091) B1480091
theorem B986875 : Blo 984595 986875 := bstep (se 1 (by rfl) ⟨740156, by rfl⟩ : syracuseStep 986875 = 1480313) B1480313
theorem B986943 : Blo 984595 986943 := bstep (se 1 (by rfl) ⟨740207, by rfl⟩ : syracuseStep 986943 = 1480415) B1480415
theorem B987007 : Blo 984595 987007 := bstep (se 1 (by rfl) ⟨740255, by rfl⟩ : syracuseStep 987007 = 1480511) B1480511
theorem B1478639 : Blo 984595 1478639 := bstep (se 1 (by rfl) ⟨1108979, by rfl⟩ : syracuseStep 1478639 = 2217959) B2217959
theorem B987119 : Blo 984595 987119 := bstep (se 1 (by rfl) ⟨740339, by rfl⟩ : syracuseStep 987119 = 1480679) B1480679
theorem B1478651 : Blo 984595 1478651 := bstep (se 1 (by rfl) ⟨1108988, by rfl⟩ : syracuseStep 1478651 = 2217977) B2217977
theorem B987131 : Blo 984595 987131 := bstep (se 1 (by rfl) ⟨740348, by rfl⟩ : syracuseStep 987131 = 1480697) B1480697
theorem B1478711 : Blo 984595 1478711 := bstep (se 1 (by rfl) ⟨1109033, by rfl⟩ : syracuseStep 1478711 = 2218067) B2218067
theorem B987199 : Blo 984595 987199 := bstep (se 1 (by rfl) ⟨740399, by rfl⟩ : syracuseStep 987199 = 1480799) B1480799
theorem B1478759 : Blo 984595 1478759 := bstep (se 1 (by rfl) ⟨1109069, by rfl⟩ : syracuseStep 1478759 = 2218139) B2218139
theorem B987239 : Blo 984595 987239 := bstep (se 1 (by rfl) ⟨740429, by rfl⟩ : syracuseStep 987239 = 1480859) B1480859
theorem B987263 : Blo 984595 987263 := bstep (se 1 (by rfl) ⟨740447, by rfl⟩ : syracuseStep 987263 = 1480895) B1480895
theorem B1249435 : Blo 984595 1249435 := bstep (se 1 (by rfl) ⟨937076, by rfl⟩ : syracuseStep 1249435 = 1874153) B1874153
theorem B987291 : Blo 984595 987291 := bstep (se 1 (by rfl) ⟨740468, by rfl⟩ : syracuseStep 987291 = 1480937) B1480937
theorem B1478831 : Blo 984595 1478831 := bstep (se 1 (by rfl) ⟨1109123, by rfl⟩ : syracuseStep 1478831 = 2218247) B2218247
theorem B3903677 : Blo 984595 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B987495 : Blo 984595 987495 := bstep (se 1 (by rfl) ⟨740621, by rfl⟩ : syracuseStep 987495 = 1481243) B1481243
theorem B17994089 : Blo 984595 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B1479035 : Blo 984595 1479035 := bstep (se 1 (by rfl) ⟨1109276, by rfl⟩ : syracuseStep 1479035 = 2218553) B2218553
theorem B987547 : Blo 984595 987547 := bstep (se 1 (by rfl) ⟨740660, by rfl⟩ : syracuseStep 987547 = 1481321) B1481321
theorem B1479305 : Blo 984595 1479305 := bstep (se 2 (by rfl) ⟨554739, by rfl⟩ : syracuseStep 1479305 = 1109479) B1109479
theorem B987899 : Blo 984595 987899 := bstep (se 1 (by rfl) ⟨740924, by rfl⟩ : syracuseStep 987899 = 1481849) B1481849
theorem B987967 : Blo 984595 987967 := bstep (se 1 (by rfl) ⟨740975, by rfl⟩ : syracuseStep 987967 = 1481951) B1481951
theorem B4264787 : Blo 984595 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B1479515 : Blo 984595 1479515 := bstep (se 1 (by rfl) ⟨1109636, by rfl⟩ : syracuseStep 1479515 = 2219273) B2219273
theorem B987995 : Blo 984595 987995 := bstep (se 1 (by rfl) ⟨740996, by rfl⟩ : syracuseStep 987995 = 1481993) B1481993
theorem B988063 : Blo 984595 988063 := bstep (se 1 (by rfl) ⟨741047, by rfl⟩ : syracuseStep 988063 = 1482095) B1482095
theorem B988143 : Blo 984595 988143 := bstep (se 1 (by rfl) ⟨741107, by rfl⟩ : syracuseStep 988143 = 1482215) B1482215
theorem B1053767 : Blo 984595 1053767 := bstep (se 1 (by rfl) ⟨790325, by rfl⟩ : syracuseStep 1053767 = 1580651) B1580651
theorem B988231 : Blo 984595 988231 := bstep (se 1 (by rfl) ⟨741173, by rfl⟩ : syracuseStep 988231 = 1482347) B1482347
theorem B988315 : Blo 984595 988315 := bstep (se 1 (by rfl) ⟨741236, by rfl⟩ : syracuseStep 988315 = 1482473) B1482473
theorem B6329573 : Blo 984595 6329573 := bstep (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) B1186795
theorem B988411 : Blo 984595 988411 := bstep (se 1 (by rfl) ⟨741308, by rfl⟩ : syracuseStep 988411 = 1482617) B1482617
theorem B1479977 : Blo 984595 1479977 := bstep (se 2 (by rfl) ⟨554991, by rfl⟩ : syracuseStep 1479977 = 1109983) B1109983
theorem B988479 : Blo 984595 988479 := bstep (se 1 (by rfl) ⟨741359, by rfl⟩ : syracuseStep 988479 = 1482719) B1482719
theorem B1480175 : Blo 984595 1480175 := bstep (se 1 (by rfl) ⟨1110131, by rfl⟩ : syracuseStep 1480175 = 2220263) B2220263
theorem B10131115 : Blo 984595 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B2496379 : Blo 984595 2496379 := bstep (se 1 (by rfl) ⟨1872284, by rfl⟩ : syracuseStep 2496379 = 3744569) B3744569
theorem B1480571 : Blo 984595 1480571 := bstep (se 1 (by rfl) ⟨1110428, by rfl⟩ : syracuseStep 1480571 = 2220857) B2220857
theorem B8427401 : Blo 984595 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B1480607 : Blo 984595 1480607 := bstep (se 1 (by rfl) ⟨1110455, by rfl⟩ : syracuseStep 1480607 = 2220911) B2220911
theorem B3741821 : Blo 984595 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B1480841 : Blo 984595 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B1480991 : Blo 984595 1480991 := bstep (se 1 (by rfl) ⟨1110743, by rfl⟩ : syracuseStep 1480991 = 2221487) B2221487
theorem B2136377 : Blo 984595 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B4495711 : Blo 984595 4495711 := bstep (se 1 (by rfl) ⟨3371783, by rfl⟩ : syracuseStep 4495711 = 6743567) B6743567
theorem B1874335 : Blo 984595 1874335 := bstep (se 1 (by rfl) ⟨1405751, by rfl⟩ : syracuseStep 1874335 = 2811503) B2811503
theorem B8985367 : Blo 984595 8985367 := bstep (se 1 (by rfl) ⟨6739025, by rfl⟩ : syracuseStep 8985367 = 13478051) B13478051
theorem B1481543 : Blo 984595 1481543 := bstep (se 1 (by rfl) ⟨1111157, by rfl⟩ : syracuseStep 1481543 = 2222315) B2222315
theorem B2366489 : Blo 984595 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2366671 : Blo 984595 2366671 := bstep (se 1 (by rfl) ⟨1775003, by rfl⟩ : syracuseStep 2366671 = 3550007) B3550007
theorem B2661703 : Blo 984595 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B18030073 : Blo 984595 18030073 := bstep (se 2 (by rfl) ⟨6761277, by rfl⟩ : syracuseStep 18030073 = 13522555) B13522555
theorem B1482407 : Blo 984595 1482407 := bstep (se 1 (by rfl) ⟨1111805, by rfl⟩ : syracuseStep 1482407 = 2223611) B2223611
theorem B28450547 : Blo 984595 28450547 := bstep (se 1 (by rfl) ⟨21337910, by rfl⟩ : syracuseStep 28450547 = 42675821) B42675821
theorem B1482527 : Blo 984595 1482527 := bstep (se 1 (by rfl) ⟨1111895, by rfl⟩ : syracuseStep 1482527 = 2223791) B2223791
theorem B2105185 : Blo 984595 2105185 := bstep (se 2 (by rfl) ⟨789444, by rfl⟩ : syracuseStep 2105185 = 1578889) B1578889
theorem B7118927 : Blo 984595 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B5611751 : Blo 984595 5611751 := bstep (se 1 (by rfl) ⟨4208813, by rfl⟩ : syracuseStep 5611751 = 8417627) B8417627
theorem B1876279 : Blo 984595 1876279 := bstep (se 1 (by rfl) ⟨1407209, by rfl⟩ : syracuseStep 1876279 = 2814419) B2814419
theorem B16195945 : Blo 984595 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B2367881 : Blo 984595 2367881 := bstep (se 2 (by rfl) ⟨887955, by rfl⟩ : syracuseStep 2367881 = 1775911) B1775911
theorem B9478903 : Blo 984595 9478903 := bstep (se 1 (by rfl) ⟨7109177, by rfl⟩ : syracuseStep 9478903 = 14218355) B14218355
theorem B6005623 : Blo 984595 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B2106415 : Blo 984595 2106415 := bstep (se 1 (by rfl) ⟨1579811, by rfl⟩ : syracuseStep 2106415 = 3159623) B3159623
theorem B8987705 : Blo 984595 8987705 := bstep (se 2 (by rfl) ⟨3370389, by rfl⟩ : syracuseStep 8987705 = 6740779) B6740779
theorem B1582201 : Blo 984595 1582201 := bstep (se 2 (by rfl) ⟨593325, by rfl⟩ : syracuseStep 1582201 = 1186651) B1186651
theorem B3745223 : Blo 984595 3745223 := bstep (se 1 (by rfl) ⟨2808917, by rfl⟩ : syracuseStep 3745223 = 5617835) B5617835
theorem B7480997 : Blo 984595 7480997 := bstep (se 4 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 7480997 = 1402687) B1402687
theorem B73869143 : Blo 984595 73869143 := bstep (se 1 (by rfl) ⟨55401857, by rfl⟩ : syracuseStep 73869143 = 110803715) B110803715
theorem B1779833 : Blo 984595 1779833 := bstep (se 2 (by rfl) ⟨667437, by rfl⟩ : syracuseStep 1779833 = 1334875) B1334875
theorem B3746027 : Blo 984595 3746027 := bstep (se 1 (by rfl) ⟨2809520, by rfl⟩ : syracuseStep 3746027 = 5619041) B5619041
theorem B11708833 : Blo 984595 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B2107961 : Blo 984595 2107961 := bstep (se 2 (by rfl) ⟨790485, by rfl⟩ : syracuseStep 2107961 = 1580971) B1580971
theorem B7121465 : Blo 984595 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B2370131 : Blo 984595 2370131 := bstep (se 1 (by rfl) ⟨1777598, by rfl⟩ : syracuseStep 2370131 = 3555197) B3555197
theorem B5778383 : Blo 984595 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B12659813 : Blo 984595 12659813 := bstep (se 4 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 12659813 = 2373715) B2373715
theorem B12791033 : Blo 984595 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B18984253 : Blo 984595 18984253 := bstep (se 3 (by rfl) ⟨3559547, by rfl⟩ : syracuseStep 18984253 = 7119095) B7119095
theorem B1519609 : Blo 984595 1519609 := bstep (se 2 (by rfl) ⟨569853, by rfl⟩ : syracuseStep 1519609 = 1139707) B1139707
theorem B3158291 : Blo 984595 3158291 := bstep (se 1 (by rfl) ⟨2368718, by rfl⟩ : syracuseStep 3158291 = 4737437) B4737437
theorem B3748139 : Blo 984595 3748139 := bstep (se 1 (by rfl) ⟨2811104, by rfl⟩ : syracuseStep 3748139 = 5622209) B5622209
theorem B5059135 : Blo 984595 5059135 := bstep (se 1 (by rfl) ⟨3794351, by rfl⟩ : syracuseStep 5059135 = 7588703) B7588703
theorem B6009851 : Blo 984595 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B4994945 : Blo 984595 4994945 := bstep (se 2 (by rfl) ⟨1873104, by rfl⟩ : syracuseStep 4994945 = 3746209) B3746209
theorem B5617583 : Blo 984595 5617583 := bstep (se 1 (by rfl) ⟨4213187, by rfl⟩ : syracuseStep 5617583 = 8426375) B8426375
theorem B3553321 : Blo 984595 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B3651655 : Blo 984595 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B65649305 : Blo 984595 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B4995755 : Blo 984595 4995755 := bstep (se 1 (by rfl) ⟨3746816, by rfl⟩ : syracuseStep 4995755 = 7493633) B7493633
theorem B2374379 : Blo 984595 2374379 := bstep (se 1 (by rfl) ⟨1780784, by rfl⟩ : syracuseStep 2374379 = 3561569) B3561569
theorem B3750887 : Blo 984595 3750887 := bstep (se 1 (by rfl) ⟨2813165, by rfl⟩ : syracuseStep 3750887 = 5626331) B5626331
theorem B4996241 : Blo 984595 4996241 := bstep (se 2 (by rfl) ⟨1873590, by rfl⟩ : syracuseStep 4996241 = 3747181) B3747181
theorem B4209907 : Blo 984595 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B4734377 : Blo 984595 4734377 := bstep (se 2 (by rfl) ⟨1775391, by rfl⟩ : syracuseStep 4734377 = 3550783) B3550783
theorem B2670007 : Blo 984595 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B4734571 : Blo 984595 4734571 := bstep (se 1 (by rfl) ⟨3550928, by rfl⟩ : syracuseStep 4734571 = 7101857) B7101857
theorem B3554923 : Blo 984595 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B4210643 : Blo 984595 4210643 := bstep (se 1 (by rfl) ⟨3157982, by rfl⟩ : syracuseStep 4210643 = 6315965) B6315965
theorem B14434735 : Blo 984595 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B4506221 : Blo 984595 4506221 := bstep (se 3 (by rfl) ⟨844916, by rfl⟩ : syracuseStep 4506221 = 1689833) B1689833
theorem B71877395 : Blo 984595 71877395 := bstep (se 1 (by rfl) ⟨53908046, by rfl⟩ : syracuseStep 71877395 = 107816093) B107816093
theorem B5620499 : Blo 984595 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B8438813 : Blo 984595 8438813 := bstep (se 3 (by rfl) ⟨1582277, by rfl⟩ : syracuseStep 8438813 = 3164555) B3164555
theorem B3752999 : Blo 984595 3752999 := bstep (se 1 (by rfl) ⟨2814749, by rfl⟩ : syracuseStep 3752999 = 5629499) B5629499
theorem B8995951 : Blo 984595 8995951 := bstep (se 1 (by rfl) ⟨6746963, by rfl⟩ : syracuseStep 8995951 = 13493927) B13493927
theorem B4998671 : Blo 984595 4998671 := bstep (se 1 (by rfl) ⟨3749003, by rfl⟩ : syracuseStep 4998671 = 7498007) B7498007
theorem B4212283 : Blo 984595 4212283 := bstep (se 1 (by rfl) ⟨3159212, by rfl⟩ : syracuseStep 4212283 = 6318425) B6318425
theorem B187582067 : Blo 984595 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B55428907 : Blo 984595 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B7489745 : Blo 984595 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B4999481 : Blo 984595 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B5065067 : Blo 984595 5065067 := bstep (se 1 (by rfl) ⟨3798800, by rfl⟩ : syracuseStep 5065067 = 7597601) B7597601
theorem B12634541 : Blo 984595 12634541 := bstep (se 3 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 12634541 = 4737953) B4737953
theorem B2804327 : Blo 984595 2804327 := bstep (se 1 (by rfl) ⟨2103245, by rfl⟩ : syracuseStep 2804327 = 4206491) B4206491
theorem B8440523 : Blo 984595 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B4213529 : Blo 984595 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B3558455 : Blo 984595 3558455 := bstep (se 1 (by rfl) ⟨2668841, by rfl⟩ : syracuseStep 3558455 = 5337683) B5337683
theorem B5622959 : Blo 984595 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B3329639 : Blo 984595 3329639 := bstep (se 1 (by rfl) ⟨2497229, by rfl⟩ : syracuseStep 3329639 = 4994459) B4994459
theorem B4509287 : Blo 984595 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B3166427 : Blo 984595 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B5329289 : Blo 984595 5329289 := bstep (se 2 (by rfl) ⟨1998483, by rfl⟩ : syracuseStep 5329289 = 3996967) B3996967
theorem B7492175 : Blo 984595 7492175 := bstep (se 1 (by rfl) ⟨5619131, by rfl⟩ : syracuseStep 7492175 = 11238263) B11238263
theorem B6411419 : Blo 984595 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B2217167 : Blo 984595 2217167 := bstep (se 1 (by rfl) ⟨1662875, by rfl⟩ : syracuseStep 2217167 = 3325751) B3325751
theorem B2217257 : Blo 984595 2217257 := bstep (se 2 (by rfl) ⟨831471, by rfl⟩ : syracuseStep 2217257 = 1662943) B1662943
theorem B8443187 : Blo 984595 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B2217455 : Blo 984595 2217455 := bstep (se 1 (by rfl) ⟨1663091, by rfl⟩ : syracuseStep 2217455 = 3326183) B3326183
theorem B7984919 : Blo 984595 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B2217851 : Blo 984595 2217851 := bstep (se 1 (by rfl) ⟨1663388, by rfl⟩ : syracuseStep 2217851 = 3326777) B3326777
theorem B2217887 : Blo 984595 2217887 := bstep (se 1 (by rfl) ⟨1663415, by rfl⟩ : syracuseStep 2217887 = 3326831) B3326831
theorem B2218121 : Blo 984595 2218121 := bstep (se 2 (by rfl) ⟨831795, by rfl⟩ : syracuseStep 2218121 = 1663591) B1663591
theorem B2218337 : Blo 984595 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B11393405 : Blo 984595 11393405 := bstep (se 3 (by rfl) ⟨2136263, by rfl⟩ : syracuseStep 11393405 = 4272527) B4272527
theorem B2218427 : Blo 984595 2218427 := bstep (se 1 (by rfl) ⟨1663820, by rfl⟩ : syracuseStep 2218427 = 3327641) B3327641
theorem B18930125 : Blo 984595 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B2218823 : Blo 984595 2218823 := bstep (se 1 (by rfl) ⟨1664117, by rfl⟩ : syracuseStep 2218823 = 3328235) B3328235
theorem B13523921 : Blo 984595 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B2219129 : Blo 984595 2219129 := bstep (se 2 (by rfl) ⟨832173, by rfl⟩ : syracuseStep 2219129 = 1664347) B1664347
theorem B2219687 : Blo 984595 2219687 := bstep (se 1 (by rfl) ⟨1664765, by rfl⟩ : syracuseStep 2219687 = 3329531) B3329531
theorem B2219795 : Blo 984595 2219795 := bstep (se 1 (by rfl) ⟨1664846, by rfl⟩ : syracuseStep 2219795 = 3329693) B3329693
theorem B4218655 : Blo 984595 4218655 := bstep (se 1 (by rfl) ⟨3163991, by rfl⟩ : syracuseStep 4218655 = 6327983) B6327983
theorem B7987187 : Blo 984595 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B2220155 : Blo 984595 2220155 := bstep (se 1 (by rfl) ⟨1665116, by rfl⟩ : syracuseStep 2220155 = 3330233) B3330233
theorem B2220425 : Blo 984595 2220425 := bstep (se 2 (by rfl) ⟨832659, by rfl⟩ : syracuseStep 2220425 = 1665319) B1665319
theorem B3334823 : Blo 984595 3334823 := bstep (se 1 (by rfl) ⟨2501117, by rfl⟩ : syracuseStep 3334823 = 5002235) B5002235
theorem B3335147 : Blo 984595 3335147 := bstep (se 1 (by rfl) ⟨2501360, by rfl⟩ : syracuseStep 3335147 = 5002721) B5002721
theorem B2221559 : Blo 984595 2221559 := bstep (se 1 (by rfl) ⟨1666169, by rfl⟩ : syracuseStep 2221559 = 3332339) B3332339
theorem B2221595 : Blo 984595 2221595 := bstep (se 1 (by rfl) ⟨1666196, by rfl⟩ : syracuseStep 2221595 = 3332393) B3332393
theorem B1107751 : Blo 984595 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B5629931 : Blo 984595 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B3336335 : Blo 984595 3336335 := bstep (se 1 (by rfl) ⟨2502251, by rfl⟩ : syracuseStep 3336335 = 5004503) B5004503
theorem B1665515 : Blo 984595 1665515 := bstep (se 1 (by rfl) ⟨1249136, by rfl⟩ : syracuseStep 1665515 = 2498273) B2498273
theorem B2222585 : Blo 984595 2222585 := bstep (se 2 (by rfl) ⟨833469, by rfl⟩ : syracuseStep 2222585 = 1666939) B1666939
theorem B2222639 : Blo 984595 2222639 := bstep (se 1 (by rfl) ⟨1666979, by rfl⟩ : syracuseStep 2222639 = 3333959) B3333959
theorem B2222675 : Blo 984595 2222675 := bstep (se 1 (by rfl) ⟨1667006, by rfl⟩ : syracuseStep 2222675 = 3334013) B3334013
theorem B2222855 : Blo 984595 2222855 := bstep (se 1 (by rfl) ⟨1667141, by rfl⟩ : syracuseStep 2222855 = 3334283) B3334283
theorem B2223071 : Blo 984595 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B1666217 : Blo 984595 1666217 := bstep (se 2 (by rfl) ⟨624831, by rfl⟩ : syracuseStep 1666217 = 1249663) B1249663
theorem B2223287 : Blo 984595 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B4222313 : Blo 984595 4222313 := bstep (se 2 (by rfl) ⟨1583367, by rfl⟩ : syracuseStep 4222313 = 3166735) B3166735
theorem B1404487 : Blo 984595 1404487 := bstep (se 1 (by rfl) ⟨1053365, by rfl⟩ : syracuseStep 1404487 = 2106731) B2106731
theorem B8416943 : Blo 984595 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B7499465 : Blo 984595 7499465 := bstep (se 2 (by rfl) ⟨2812299, by rfl⟩ : syracuseStep 7499465 = 5624599) B5624599
theorem B2223863 : Blo 984595 2223863 := bstep (se 1 (by rfl) ⟨1667897, by rfl⟩ : syracuseStep 2223863 = 3335795) B3335795
theorem B1666811 : Blo 984595 1666811 := bstep (se 1 (by rfl) ⟨1250108, by rfl⟩ : syracuseStep 1666811 = 2500217) B2500217
theorem B2223935 : Blo 984595 2223935 := bstep (se 1 (by rfl) ⟨1667951, by rfl⟩ : syracuseStep 2223935 = 3335903) B3335903
theorem B2224043 : Blo 984595 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B11235347 : Blo 984595 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B5337161 : Blo 984595 5337161 := bstep (se 2 (by rfl) ⟨2001435, by rfl⟩ : syracuseStep 5337161 = 4002871) B4002871
theorem B1110847 : Blo 984595 1110847 := bstep (se 1 (by rfl) ⟨833135, by rfl⟩ : syracuseStep 1110847 = 1666271) B1666271
theorem B18969491 : Blo 984595 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B1405945 : Blo 984595 1405945 := bstep (se 2 (by rfl) ⟨527229, by rfl⟩ : syracuseStep 1405945 = 1054459) B1054459
theorem B1111135 : Blo 984595 1111135 := bstep (se 1 (by rfl) ⟨833351, by rfl⟩ : syracuseStep 1111135 = 1666703) B1666703
theorem B18970037 : Blo 984595 18970037 := bstep (se 5 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 18970037 = 1778441) B1778441
theorem B4749025 : Blo 984595 4749025 := bstep (se 2 (by rfl) ⟨1780884, by rfl⟩ : syracuseStep 4749025 = 3561769) B3561769
theorem B590674961 : Blo 984595 590674961 := bstep (se 2 (by rfl) ⟨221503110, by rfl⟩ : syracuseStep 590674961 = 443006221) B443006221
theorem B1998047 : Blo 984595 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B21594593 : Blo 984595 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B11994601 : Blo 984595 11994601 := bstep (se 2 (by rfl) ⟨4497975, by rfl⟩ : syracuseStep 11994601 = 8995951) B8995951
theorem B1246747 : Blo 984595 1246747 := bstep (se 1 (by rfl) ⟨935060, by rfl⟩ : syracuseStep 1246747 = 1870121) B1870121
theorem B3376711 : Blo 984595 3376711 := bstep (se 1 (by rfl) ⟨2532533, by rfl⟩ : syracuseStep 3376711 = 5065067) B5065067
theorem B8423027 : Blo 984595 8423027 := bstep (se 1 (by rfl) ⟨6317270, by rfl⟩ : syracuseStep 8423027 = 12634541) B12634541
theorem B1869551 : Blo 984595 1869551 := bstep (se 1 (by rfl) ⟨1402163, by rfl⟩ : syracuseStep 1869551 = 2804327) B2804327
theorem B984815 : Blo 984595 984815 := bstep (se 1 (by rfl) ⟨738611, by rfl⟩ : syracuseStep 984815 = 1477223) B1477223
theorem B984943 : Blo 984595 984943 := bstep (se 1 (by rfl) ⟨738707, by rfl⟩ : syracuseStep 984943 = 1477415) B1477415
theorem B1247167 : Blo 984595 1247167 := bstep (se 1 (by rfl) ⟨935375, by rfl⟩ : syracuseStep 1247167 = 1870751) B1870751
theorem B985159 : Blo 984595 985159 := bstep (se 1 (by rfl) ⟨738869, by rfl⟩ : syracuseStep 985159 = 1477739) B1477739
theorem B985319 : Blo 984595 985319 := bstep (se 1 (by rfl) ⟨738989, by rfl⟩ : syracuseStep 985319 = 1477979) B1477979
theorem B985339 : Blo 984595 985339 := bstep (se 1 (by rfl) ⟨739004, by rfl⟩ : syracuseStep 985339 = 1478009) B1478009
theorem B985343 : Blo 984595 985343 := bstep (se 1 (by rfl) ⟨739007, by rfl⟩ : syracuseStep 985343 = 1478015) B1478015
theorem B2492795 : Blo 984595 2492795 := bstep (se 1 (by rfl) ⟨1869596, by rfl⟩ : syracuseStep 2492795 = 3739193) B3739193
theorem B1477001 : Blo 984595 1477001 := bstep (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) B1107751
theorem B985759 : Blo 984595 985759 := bstep (se 1 (by rfl) ⟨739319, by rfl⟩ : syracuseStep 985759 = 1478639) B1478639
theorem B985767 : Blo 984595 985767 := bstep (se 1 (by rfl) ⟨739325, by rfl⟩ : syracuseStep 985767 = 1478651) B1478651
theorem B985807 : Blo 984595 985807 := bstep (se 1 (by rfl) ⟨739355, by rfl⟩ : syracuseStep 985807 = 1478711) B1478711
theorem B985839 : Blo 984595 985839 := bstep (se 1 (by rfl) ⟨739379, by rfl⟩ : syracuseStep 985839 = 1478759) B1478759
theorem B985887 : Blo 984595 985887 := bstep (se 1 (by rfl) ⟨739415, by rfl⟩ : syracuseStep 985887 = 1478831) B1478831
theorem B986023 : Blo 984595 986023 := bstep (se 1 (by rfl) ⟨739517, by rfl⟩ : syracuseStep 986023 = 1479035) B1479035
theorem B986203 : Blo 984595 986203 := bstep (se 1 (by rfl) ⟨739652, by rfl⟩ : syracuseStep 986203 = 1479305) B1479305
theorem B986343 : Blo 984595 986343 := bstep (se 1 (by rfl) ⟨739757, by rfl⟩ : syracuseStep 986343 = 1479515) B1479515
theorem B1478111 : Blo 984595 1478111 := bstep (se 1 (by rfl) ⟨1108583, by rfl⟩ : syracuseStep 1478111 = 2217167) B2217167
theorem B1478171 : Blo 984595 1478171 := bstep (se 1 (by rfl) ⟨1108628, by rfl⟩ : syracuseStep 1478171 = 2217257) B2217257
theorem B986651 : Blo 984595 986651 := bstep (se 1 (by rfl) ⟨739988, by rfl⟩ : syracuseStep 986651 = 1479977) B1479977
theorem B1478303 : Blo 984595 1478303 := bstep (se 1 (by rfl) ⟨1108727, by rfl⟩ : syracuseStep 1478303 = 2217455) B2217455
theorem B986783 : Blo 984595 986783 := bstep (se 1 (by rfl) ⟨740087, by rfl⟩ : syracuseStep 986783 = 1480175) B1480175
theorem B1478567 : Blo 984595 1478567 := bstep (se 1 (by rfl) ⟨1108925, by rfl⟩ : syracuseStep 1478567 = 2217851) B2217851
theorem B987047 : Blo 984595 987047 := bstep (se 1 (by rfl) ⟨740285, by rfl⟩ : syracuseStep 987047 = 1480571) B1480571
theorem B1478591 : Blo 984595 1478591 := bstep (se 1 (by rfl) ⟨1108943, by rfl⟩ : syracuseStep 1478591 = 2217887) B2217887
theorem B987071 : Blo 984595 987071 := bstep (se 1 (by rfl) ⟨740303, by rfl⟩ : syracuseStep 987071 = 1480607) B1480607
theorem B2494547 : Blo 984595 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B1478747 : Blo 984595 1478747 := bstep (se 1 (by rfl) ⟨1109060, by rfl⟩ : syracuseStep 1478747 = 2218121) B2218121
theorem B987227 : Blo 984595 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B987327 : Blo 984595 987327 := bstep (se 1 (by rfl) ⟨740495, by rfl⟩ : syracuseStep 987327 = 1480991) B1480991
theorem B1478891 : Blo 984595 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B1478951 : Blo 984595 1478951 := bstep (se 1 (by rfl) ⟨1109213, by rfl⟩ : syracuseStep 1478951 = 2218427) B2218427
theorem B12620083 : Blo 984595 12620083 := bstep (se 1 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 12620083 = 18930125) B18930125
theorem B1479215 : Blo 984595 1479215 := bstep (se 1 (by rfl) ⟨1109411, by rfl⟩ : syracuseStep 1479215 = 2218823) B2218823
theorem B987695 : Blo 984595 987695 := bstep (se 1 (by rfl) ⟨740771, by rfl⟩ : syracuseStep 987695 = 1481543) B1481543
theorem B9015947 : Blo 984595 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B1577659 : Blo 984595 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B1479419 : Blo 984595 1479419 := bstep (se 1 (by rfl) ⟨1109564, by rfl⟩ : syracuseStep 1479419 = 2219129) B2219129
theorem B1872649 : Blo 984595 1872649 := bstep (se 2 (by rfl) ⟨702243, by rfl⟩ : syracuseStep 1872649 = 1404487) B1404487
theorem B1479791 : Blo 984595 1479791 := bstep (se 1 (by rfl) ⟨1109843, by rfl⟩ : syracuseStep 1479791 = 2219687) B2219687
theorem B988271 : Blo 984595 988271 := bstep (se 1 (by rfl) ⟨741203, by rfl⟩ : syracuseStep 988271 = 1482407) B1482407
theorem B1479863 : Blo 984595 1479863 := bstep (se 1 (by rfl) ⟨1109897, by rfl⟩ : syracuseStep 1479863 = 2219795) B2219795
theorem B988351 : Blo 984595 988351 := bstep (se 1 (by rfl) ⟨741263, by rfl⟩ : syracuseStep 988351 = 1482527) B1482527
theorem B1480103 : Blo 984595 1480103 := bstep (se 1 (by rfl) ⟨1110077, by rfl⟩ : syracuseStep 1480103 = 2220155) B2220155
theorem B3741167 : Blo 984595 3741167 := bstep (se 1 (by rfl) ⟨2805875, by rfl⟩ : syracuseStep 3741167 = 5611751) B5611751
theorem B1578587 : Blo 984595 1578587 := bstep (se 1 (by rfl) ⟨1183940, by rfl⟩ : syracuseStep 1578587 = 2367881) B2367881
theorem B1480283 : Blo 984595 1480283 := bstep (se 1 (by rfl) ⟨1110212, by rfl⟩ : syracuseStep 1480283 = 2220425) B2220425
theorem B2496815 : Blo 984595 2496815 := bstep (se 1 (by rfl) ⟨1872611, by rfl⟩ : syracuseStep 2496815 = 3745223) B3745223
theorem B1481039 : Blo 984595 1481039 := bstep (se 1 (by rfl) ⟨1110779, by rfl⟩ : syracuseStep 1481039 = 2221559) B2221559
theorem B1481063 : Blo 984595 1481063 := bstep (se 1 (by rfl) ⟨1110797, by rfl⟩ : syracuseStep 1481063 = 2221595) B2221595
theorem B1481129 : Blo 984595 1481129 := bstep (se 2 (by rfl) ⟨555423, by rfl⟩ : syracuseStep 1481129 = 1110847) B1110847
theorem B4987331 : Blo 984595 4987331 := bstep (se 1 (by rfl) ⟨3740498, by rfl⟩ : syracuseStep 4987331 = 7480997) B7480997
theorem B1874593 : Blo 984595 1874593 := bstep (se 2 (by rfl) ⟨702972, by rfl⟩ : syracuseStep 1874593 = 1405945) B1405945
theorem B1186555 : Blo 984595 1186555 := bstep (se 1 (by rfl) ⟨889916, by rfl⟩ : syracuseStep 1186555 = 1779833) B1779833
theorem B1481513 : Blo 984595 1481513 := bstep (se 2 (by rfl) ⟨555567, by rfl⟩ : syracuseStep 1481513 = 1111135) B1111135
theorem B2497351 : Blo 984595 2497351 := bstep (se 1 (by rfl) ⟨1873013, by rfl⟩ : syracuseStep 2497351 = 3746027) B3746027
theorem B1481723 : Blo 984595 1481723 := bstep (se 1 (by rfl) ⟨1111292, by rfl⟩ : syracuseStep 1481723 = 2222585) B2222585
theorem B1481759 : Blo 984595 1481759 := bstep (se 1 (by rfl) ⟨1111319, by rfl⟩ : syracuseStep 1481759 = 2222639) B2222639
theorem B14195749 : Blo 984595 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B1580087 : Blo 984595 1580087 := bstep (se 1 (by rfl) ⟨1185065, by rfl⟩ : syracuseStep 1580087 = 2370131) B2370131
theorem B1481783 : Blo 984595 1481783 := bstep (se 1 (by rfl) ⟨1111337, by rfl⟩ : syracuseStep 1481783 = 2222675) B2222675
theorem B1481903 : Blo 984595 1481903 := bstep (se 1 (by rfl) ⟨1111427, by rfl⟩ : syracuseStep 1481903 = 2222855) B2222855
theorem B1482047 : Blo 984595 1482047 := bstep (se 1 (by rfl) ⟨1111535, by rfl⟩ : syracuseStep 1482047 = 2223071) B2223071
theorem B1482191 : Blo 984595 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B8527355 : Blo 984595 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B13508153 : Blo 984595 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B6332033 : Blo 984595 6332033 := bstep (se 2 (by rfl) ⟨2374512, by rfl⟩ : syracuseStep 6332033 = 4749025) B4749025
theorem B5611295 : Blo 984595 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B1482575 : Blo 984595 1482575 := bstep (se 1 (by rfl) ⟨1111931, by rfl⟩ : syracuseStep 1482575 = 2223863) B2223863
theorem B1482623 : Blo 984595 1482623 := bstep (se 1 (by rfl) ⟨1111967, by rfl⟩ : syracuseStep 1482623 = 2223935) B2223935
theorem B1482695 : Blo 984595 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B1575133229 : Blo 984595 1575133229 := bstep (se 3 (by rfl) ⟨295337480, by rfl⟩ : syracuseStep 1575133229 = 590674961) B590674961
theorem B2105527 : Blo 984595 2105527 := bstep (se 1 (by rfl) ⟨1579145, by rfl⟩ : syracuseStep 2105527 = 3158291) B3158291
theorem B2498759 : Blo 984595 2498759 := bstep (se 1 (by rfl) ⟨1874069, by rfl⟩ : syracuseStep 2498759 = 3748139) B3748139
theorem B2499113 : Blo 984595 2499113 := bstep (se 2 (by rfl) ⟨937167, by rfl⟩ : syracuseStep 2499113 = 1874335) B1874335
theorem B4006567 : Blo 984595 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B3745055 : Blo 984595 3745055 := bstep (se 1 (by rfl) ⟨2808791, by rfl⟩ : syracuseStep 3745055 = 5617583) B5617583
theorem B3155561 : Blo 984595 3155561 := bstep (se 2 (by rfl) ⟨1183335, by rfl⟩ : syracuseStep 3155561 = 2366671) B2366671
theorem B5613209 : Blo 984595 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B1582919 : Blo 984595 1582919 := bstep (se 1 (by rfl) ⟨1187189, by rfl⟩ : syracuseStep 1582919 = 2374379) B2374379
theorem B2500591 : Blo 984595 2500591 := bstep (se 1 (by rfl) ⟨1875443, by rfl⟩ : syracuseStep 2500591 = 3750887) B3750887
theorem B3156251 : Blo 984595 3156251 := bstep (se 1 (by rfl) ⟨2367188, by rfl⟩ : syracuseStep 3156251 = 4734377) B4734377
theorem B2501705 : Blo 984595 2501705 := bstep (se 2 (by rfl) ⟨938139, by rfl⟩ : syracuseStep 2501705 = 1876279) B1876279
theorem B47918263 : Blo 984595 47918263 := bstep (se 1 (by rfl) ⟨35938697, by rfl⟩ : syracuseStep 47918263 = 71877395) B71877395
theorem B3746999 : Blo 984595 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B19246313 : Blo 984595 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B2501999 : Blo 984595 2501999 := bstep (se 1 (by rfl) ⟨1876499, by rfl⟩ : syracuseStep 2501999 = 3752999) B3752999
theorem B2665855 : Blo 984595 2665855 := bstep (se 1 (by rfl) ⟨1999391, by rfl⟩ : syracuseStep 2665855 = 3998783) B3998783
theorem B10661345 : Blo 984595 10661345 := bstep (se 2 (by rfl) ⟨3998004, by rfl⟩ : syracuseStep 10661345 = 7996009) B7996009
theorem B15216133 : Blo 984595 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B47984237 : Blo 984595 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B125054711 : Blo 984595 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B8007497 : Blo 984595 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B4993163 : Blo 984595 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B2109601 : Blo 984595 2109601 := bstep (se 2 (by rfl) ⟨791100, by rfl⟩ : syracuseStep 2109601 = 1582201) B1582201
theorem B2372303 : Blo 984595 2372303 := bstep (se 1 (by rfl) ⟨1779227, by rfl⟩ : syracuseStep 2372303 = 3558455) B3558455
theorem B5616377 : Blo 984595 5616377 := bstep (se 2 (by rfl) ⟨2106141, by rfl⟩ : syracuseStep 5616377 = 4212283) B4212283
theorem B3748639 : Blo 984595 3748639 := bstep (se 1 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 3748639 = 5622959) B5622959
theorem B73905209 : Blo 984595 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B2602451 : Blo 984595 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B2110951 : Blo 984595 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B3552859 : Blo 984595 3552859 := bstep (se 1 (by rfl) ⟨2664644, by rfl⟩ : syracuseStep 3552859 = 5329289) B5329289
theorem B4994783 : Blo 984595 4994783 := bstep (se 1 (by rfl) ⟨3746087, by rfl⟩ : syracuseStep 4994783 = 7492175) B7492175
theorem B15611777 : Blo 984595 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B4274279 : Blo 984595 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B5323279 : Blo 984595 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B5618267 : Blo 984595 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B1424251 : Blo 984595 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B25312337 : Blo 984595 25312337 := bstep (se 2 (by rfl) ⟨9492126, by rfl⟩ : syracuseStep 25312337 = 18984253) B18984253
theorem B3325049 : Blo 984595 3325049 := bstep (se 2 (by rfl) ⟨1246893, by rfl⟩ : syracuseStep 3325049 = 2493787) B2493787
theorem B3325373 : Blo 984595 3325373 := bstep (se 3 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 3325373 = 1247015) B1247015
theorem B196984381 : Blo 984595 196984381 := bstep (se 3 (by rfl) ⟨36934571, by rfl⟩ : syracuseStep 196984381 = 73869143) B73869143
theorem B5324791 : Blo 984595 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B3753287 : Blo 984595 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B8439875 : Blo 984595 8439875 := bstep (se 1 (by rfl) ⟨6329906, by rfl⟩ : syracuseStep 8439875 = 12659813) B12659813
theorem B4999643 : Blo 984595 4999643 := bstep (se 1 (by rfl) ⟨3749732, by rfl⟩ : syracuseStep 4999643 = 7499465) B7499465
theorem B3328505 : Blo 984595 3328505 := bstep (se 2 (by rfl) ⟨1248189, by rfl⟩ : syracuseStep 3328505 = 2496379) B2496379
theorem B7490231 : Blo 984595 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B3558107 : Blo 984595 3558107 := bstep (se 1 (by rfl) ⟨2668580, by rfl⟩ : syracuseStep 3558107 = 5337161) B5337161
theorem B4737761 : Blo 984595 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B4868873 : Blo 984595 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B3328829 : Blo 984595 3328829 := bstep (se 3 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 3328829 = 1248311) B1248311
theorem B5328125 : Blo 984595 5328125 := bstep (se 3 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 5328125 = 1998047) B1998047
theorem B11980489 : Blo 984595 11980489 := bstep (se 2 (by rfl) ⟨4492683, by rfl⟩ : syracuseStep 11980489 = 8985367) B8985367
theorem B3329963 : Blo 984595 3329963 := bstep (se 1 (by rfl) ⟨2497472, by rfl⟩ : syracuseStep 3329963 = 4994945) B4994945
theorem B43766203 : Blo 984595 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B3330503 : Blo 984595 3330503 := bstep (se 1 (by rfl) ⟨2497877, by rfl⟩ : syracuseStep 3330503 = 4995755) B4995755
theorem B3560009 : Blo 984595 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B24040097 : Blo 984595 24040097 := bstep (se 2 (by rfl) ⟨9015036, by rfl⟩ : syracuseStep 24040097 = 18030073) B18030073
theorem B3330827 : Blo 984595 3330827 := bstep (se 1 (by rfl) ⟨2498120, by rfl⟩ : syracuseStep 3330827 = 4996241) B4996241
theorem B6312761 : Blo 984595 6312761 := bstep (se 2 (by rfl) ⟨2367285, by rfl⟩ : syracuseStep 6312761 = 4734571) B4734571
theorem B4739897 : Blo 984595 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B5624873 : Blo 984595 5624873 := bstep (se 2 (by rfl) ⟨2109327, by rfl⟩ : syracuseStep 5624873 = 4218655) B4218655
theorem B2806913 : Blo 984595 2806913 := bstep (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) B2105185
theorem B2807095 : Blo 984595 2807095 := bstep (se 1 (by rfl) ⟨2105321, by rfl⟩ : syracuseStep 2807095 = 4210643) B4210643
theorem B3004147 : Blo 984595 3004147 := bstep (se 1 (by rfl) ⟨2253110, by rfl⟩ : syracuseStep 3004147 = 4506221) B4506221
theorem B5625875 : Blo 984595 5625875 := bstep (se 1 (by rfl) ⟨4219406, by rfl⟩ : syracuseStep 5625875 = 8438813) B8438813
theorem B12638537 : Blo 984595 12638537 := bstep (se 2 (by rfl) ⟨4739451, by rfl⟩ : syracuseStep 12638537 = 9478903) B9478903
theorem B11229515 : Blo 984595 11229515 := bstep (se 1 (by rfl) ⟨8422136, by rfl⟩ : syracuseStep 11229515 = 16844273) B16844273
theorem B3332447 : Blo 984595 3332447 := bstep (se 1 (by rfl) ⟨2499335, by rfl⟩ : syracuseStep 3332447 = 4998671) B4998671
theorem B2808553 : Blo 984595 2808553 := bstep (se 2 (by rfl) ⟨1053207, by rfl⟩ : syracuseStep 2808553 = 2106415) B2106415
theorem B76897025 : Blo 984595 76897025 := bstep (se 2 (by rfl) ⟨28836384, by rfl⟩ : syracuseStep 76897025 = 57672769) B57672769
theorem B1661735 : Blo 984595 1661735 := bstep (se 1 (by rfl) ⟨1246301, by rfl⟩ : syracuseStep 1661735 = 2492603) B2492603
theorem B3332987 : Blo 984595 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B5627015 : Blo 984595 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B2809019 : Blo 984595 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B4218587 : Blo 984595 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B2219759 : Blo 984595 2219759 := bstep (se 1 (by rfl) ⟨1664819, by rfl⟩ : syracuseStep 2219759 = 3329639) B3329639
theorem B3006191 : Blo 984595 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B2810045 : Blo 984595 2810045 := bstep (se 3 (by rfl) ⟨526883, by rfl⟩ : syracuseStep 2810045 = 1053767) B1053767
theorem B2843191 : Blo 984595 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B4219715 : Blo 984595 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B5628791 : Blo 984595 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B7595603 : Blo 984595 7595603 := bstep (se 1 (by rfl) ⟨5696702, by rfl⟩ : syracuseStep 7595603 = 11393405) B11393405
theorem B2844809 : Blo 984595 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B18967031 : Blo 984595 18967031 := bstep (se 1 (by rfl) ⟨14225273, by rfl⟩ : syracuseStep 18967031 = 28450547) B28450547
theorem B2026145 : Blo 984595 2026145 := bstep (se 2 (by rfl) ⟨759804, by rfl⟩ : syracuseStep 2026145 = 1519609) B1519609
theorem B4745951 : Blo 984595 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B1665913 : Blo 984595 1665913 := bstep (se 2 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 1665913 = 1249435) B1249435
theorem B2223215 : Blo 984595 2223215 := bstep (se 1 (by rfl) ⟨1667411, by rfl⟩ : syracuseStep 2223215 = 3334823) B3334823
theorem B2223431 : Blo 984595 2223431 := bstep (se 1 (by rfl) ⟨1667573, by rfl⟩ : syracuseStep 2223431 = 3335147) B3335147
theorem B5991803 : Blo 984595 5991803 := bstep (se 1 (by rfl) ⟨4493852, by rfl⟩ : syracuseStep 5991803 = 8987705) B8987705
theorem B6745513 : Blo 984595 6745513 := bstep (se 2 (by rfl) ⟨2529567, by rfl⟩ : syracuseStep 6745513 = 5059135) B5059135
theorem B2224223 : Blo 984595 2224223 := bstep (se 1 (by rfl) ⟨1668167, by rfl⟩ : syracuseStep 2224223 = 3336335) B3336335
theorem B1110343 : Blo 984595 1110343 := bstep (se 1 (by rfl) ⟨832757, by rfl⟩ : syracuseStep 1110343 = 1665515) B1665515
theorem B1405307 : Blo 984595 1405307 := bstep (se 1 (by rfl) ⟨1053980, by rfl⟩ : syracuseStep 1405307 = 2107961) B2107961
theorem B4747643 : Blo 984595 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B1110811 : Blo 984595 1110811 := bstep (se 1 (by rfl) ⟨833108, by rfl⟩ : syracuseStep 1110811 = 1666217) B1666217
theorem B2814875 : Blo 984595 2814875 := bstep (se 1 (by rfl) ⟨2111156, by rfl⟩ : syracuseStep 2814875 = 4222313) B4222313
theorem B1111207 : Blo 984595 1111207 := bstep (se 1 (by rfl) ⟨833405, by rfl⟩ : syracuseStep 1111207 = 1666811) B1666811
theorem B5994281 : Blo 984595 5994281 := bstep (se 2 (by rfl) ⟨2247855, by rfl⟩ : syracuseStep 5994281 = 4495711) B4495711
theorem B12646327 : Blo 984595 12646327 := bstep (se 1 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 12646327 = 18969491) B18969491
theorem B12646691 : Blo 984595 12646691 := bstep (se 1 (by rfl) ⟨9485018, by rfl⟩ : syracuseStep 12646691 = 18970037) B18970037
theorem B61636085 : Blo 984595 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B1246367 : Blo 984595 1246367 := bstep (se 1 (by rfl) ⟨934775, by rfl⟩ : syracuseStep 1246367 = 1869551) B1869551
theorem B984667 : Blo 984595 984667 := bstep (se 1 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 984667 = 1477001) B1477001
theorem B3245915 : Blo 984595 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B15992801 : Blo 984595 15992801 := bstep (se 2 (by rfl) ⟨5997300, by rfl⟩ : syracuseStep 15992801 = 11994601) B11994601
theorem B985407 : Blo 984595 985407 := bstep (se 1 (by rfl) ⟨739055, by rfl⟩ : syracuseStep 985407 = 1478111) B1478111
theorem B985447 : Blo 984595 985447 := bstep (se 1 (by rfl) ⟨739085, by rfl⟩ : syracuseStep 985447 = 1478171) B1478171
theorem B985535 : Blo 984595 985535 := bstep (se 1 (by rfl) ⟨739151, by rfl⟩ : syracuseStep 985535 = 1478303) B1478303
theorem B985711 : Blo 984595 985711 := bstep (se 1 (by rfl) ⟨739283, by rfl⟩ : syracuseStep 985711 = 1478567) B1478567
theorem B985727 : Blo 984595 985727 := bstep (se 1 (by rfl) ⟨739295, by rfl⟩ : syracuseStep 985727 = 1478591) B1478591
theorem B985831 : Blo 984595 985831 := bstep (se 1 (by rfl) ⟨739373, by rfl⟩ : syracuseStep 985831 = 1478747) B1478747
theorem B985927 : Blo 984595 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B985967 : Blo 984595 985967 := bstep (se 1 (by rfl) ⟨739475, by rfl⟩ : syracuseStep 985967 = 1478951) B1478951
theorem B986143 : Blo 984595 986143 := bstep (se 1 (by rfl) ⟨739607, by rfl⟩ : syracuseStep 986143 = 1479215) B1479215
theorem B16026731 : Blo 984595 16026731 := bstep (se 1 (by rfl) ⟨12020048, by rfl⟩ : syracuseStep 16026731 = 24040097) B24040097
theorem B986279 : Blo 984595 986279 := bstep (se 1 (by rfl) ⟨739709, by rfl⟩ : syracuseStep 986279 = 1479419) B1479419
theorem B986527 : Blo 984595 986527 := bstep (se 1 (by rfl) ⟨739895, by rfl⟩ : syracuseStep 986527 = 1479791) B1479791
theorem B1871275 : Blo 984595 1871275 := bstep (se 1 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 1871275 = 2806913) B2806913
theorem B986575 : Blo 984595 986575 := bstep (se 1 (by rfl) ⟨739931, by rfl⟩ : syracuseStep 986575 = 1479863) B1479863
theorem B21368357 : Blo 984595 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B986735 : Blo 984595 986735 := bstep (se 1 (by rfl) ⟨740051, by rfl⟩ : syracuseStep 986735 = 1480103) B1480103
theorem B2494111 : Blo 984595 2494111 := bstep (se 1 (by rfl) ⟨1870583, by rfl⟩ : syracuseStep 2494111 = 3741167) B3741167
theorem B986855 : Blo 984595 986855 := bstep (se 1 (by rfl) ⟨740141, by rfl⟩ : syracuseStep 986855 = 1480283) B1480283
theorem B8425691 : Blo 984595 8425691 := bstep (se 1 (by rfl) ⟨6319268, by rfl⟩ : syracuseStep 8425691 = 12638537) B12638537
theorem B987359 : Blo 984595 987359 := bstep (se 1 (by rfl) ⟨740519, by rfl⟩ : syracuseStep 987359 = 1481039) B1481039
theorem B987375 : Blo 984595 987375 := bstep (se 1 (by rfl) ⟨740531, by rfl⟩ : syracuseStep 987375 = 1481063) B1481063
theorem B987419 : Blo 984595 987419 := bstep (se 1 (by rfl) ⟨740564, by rfl⟩ : syracuseStep 987419 = 1481129) B1481129
theorem B987675 : Blo 984595 987675 := bstep (se 1 (by rfl) ⟨740756, by rfl⟩ : syracuseStep 987675 = 1481513) B1481513
theorem B987815 : Blo 984595 987815 := bstep (se 1 (by rfl) ⟨740861, by rfl⟩ : syracuseStep 987815 = 1481723) B1481723
theorem B20288177 : Blo 984595 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B987839 : Blo 984595 987839 := bstep (se 1 (by rfl) ⟨740879, by rfl⟩ : syracuseStep 987839 = 1481759) B1481759
theorem B987855 : Blo 984595 987855 := bstep (se 1 (by rfl) ⟨740891, by rfl⟩ : syracuseStep 987855 = 1481783) B1481783
theorem B987935 : Blo 984595 987935 := bstep (se 1 (by rfl) ⟨740951, by rfl⟩ : syracuseStep 987935 = 1481903) B1481903
theorem B988031 : Blo 984595 988031 := bstep (se 1 (by rfl) ⟨741023, by rfl⟩ : syracuseStep 988031 = 1482047) B1482047
theorem B988127 : Blo 984595 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B1479839 : Blo 984595 1479839 := bstep (se 1 (by rfl) ⟨1109879, by rfl⟩ : syracuseStep 1479839 = 2219759) B2219759
theorem B3740863 : Blo 984595 3740863 := bstep (se 1 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 3740863 = 5611295) B5611295
theorem B988383 : Blo 984595 988383 := bstep (se 1 (by rfl) ⟨741287, by rfl⟩ : syracuseStep 988383 = 1482575) B1482575
theorem B988415 : Blo 984595 988415 := bstep (se 1 (by rfl) ⟨741311, by rfl⟩ : syracuseStep 988415 = 1482623) B1482623
theorem B988463 : Blo 984595 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B1873363 : Blo 984595 1873363 := bstep (se 1 (by rfl) ⟨1405022, by rfl⟩ : syracuseStep 1873363 = 2810045) B2810045
theorem B1480457 : Blo 984595 1480457 := bstep (se 2 (by rfl) ⟨555171, by rfl⟩ : syracuseStep 1480457 = 1110343) B1110343
theorem B2496703 : Blo 984595 2496703 := bstep (se 1 (by rfl) ⟨1872527, by rfl⟩ : syracuseStep 2496703 = 3745055) B3745055
theorem B2103545 : Blo 984595 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B2496865 : Blo 984595 2496865 := bstep (se 2 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 2496865 = 1872649) B1872649
theorem B1481081 : Blo 984595 1481081 := bstep (se 2 (by rfl) ⟨555405, by rfl⟩ : syracuseStep 1481081 = 1110811) B1110811
theorem B2103707 : Blo 984595 2103707 := bstep (se 1 (by rfl) ⟨1577780, by rfl⟩ : syracuseStep 2103707 = 3155561) B3155561
theorem B3742139 : Blo 984595 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B1055279 : Blo 984595 1055279 := bstep (se 1 (by rfl) ⟨791459, by rfl⟩ : syracuseStep 1055279 = 1582919) B1582919
theorem B1481609 : Blo 984595 1481609 := bstep (se 2 (by rfl) ⟨555603, by rfl⟩ : syracuseStep 1481609 = 1111207) B1111207
theorem B3742793 : Blo 984595 3742793 := bstep (se 2 (by rfl) ⟨1403547, by rfl⟩ : syracuseStep 3742793 = 2807095) B2807095
theorem B1350763 : Blo 984595 1350763 := bstep (se 1 (by rfl) ⟨1013072, by rfl⟩ : syracuseStep 1350763 = 2026145) B2026145
theorem B1482143 : Blo 984595 1482143 := bstep (se 1 (by rfl) ⟨1111607, by rfl⟩ : syracuseStep 1482143 = 2223215) B2223215
theorem B2497999 : Blo 984595 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B1482287 : Blo 984595 1482287 := bstep (se 1 (by rfl) ⟨1111715, by rfl⟩ : syracuseStep 1482287 = 2223431) B2223431
theorem B31989491 : Blo 984595 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B83369807 : Blo 984595 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B1482815 : Blo 984595 1482815 := bstep (se 1 (by rfl) ⟨1112111, by rfl⟩ : syracuseStep 1482815 = 2224223) B2224223
theorem B1581535 : Blo 984595 1581535 := bstep (se 1 (by rfl) ⟨1186151, by rfl⟩ : syracuseStep 1581535 = 2372303) B2372303
theorem B3744251 : Blo 984595 3744251 := bstep (se 1 (by rfl) ⟨2808188, by rfl⟩ : syracuseStep 3744251 = 5616377) B5616377
theorem B1876583 : Blo 984595 1876583 := bstep (se 1 (by rfl) ⟨1407437, by rfl⟩ : syracuseStep 1876583 = 2814875) B2814875
theorem B2499457 : Blo 984595 2499457 := bstep (se 2 (by rfl) ⟨937296, by rfl⟩ : syracuseStep 2499457 = 1874593) B1874593
theorem B3744737 : Blo 984595 3744737 := bstep (se 2 (by rfl) ⟨1404276, by rfl⟩ : syracuseStep 3744737 = 2808553) B2808553
theorem B1582073 : Blo 984595 1582073 := bstep (se 2 (by rfl) ⟨593277, by rfl⟩ : syracuseStep 1582073 = 1186555) B1186555
theorem B8431127 : Blo 984595 8431127 := bstep (se 1 (by rfl) ⟨6323345, by rfl⟩ : syracuseStep 8431127 = 12646691) B12646691
theorem B3745511 : Blo 984595 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B262645841 : Blo 984595 262645841 := bstep (se 2 (by rfl) ⟨98492190, by rfl⟩ : syracuseStep 262645841 = 196984381) B196984381
theorem B14396395 : Blo 984595 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B2502191 : Blo 984595 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B3747485 : Blo 984595 3747485 := bstep (se 3 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 3747485 = 1405307) B1405307
theorem B5615351 : Blo 984595 5615351 := bstep (se 1 (by rfl) ⟨4211513, by rfl⟩ : syracuseStep 5615351 = 8423027) B8423027
theorem B4993487 : Blo 984595 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B3158507 : Blo 984595 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B3552083 : Blo 984595 3552083 := bstep (se 1 (by rfl) ⟨2664062, by rfl⟩ : syracuseStep 3552083 = 5328125) B5328125
theorem B6010631 : Blo 984595 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B4208507 : Blo 984595 4208507 := bstep (se 1 (by rfl) ⟨3156380, by rfl⟩ : syracuseStep 4208507 = 6312761) B6312761
theorem B3159931 : Blo 984595 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B3749915 : Blo 984595 3749915 := bstep (se 1 (by rfl) ⟨2812436, by rfl⟩ : syracuseStep 3749915 = 5624873) B5624873
theorem B3750583 : Blo 984595 3750583 := bstep (se 1 (by rfl) ⟨2812937, by rfl⟩ : syracuseStep 3750583 = 5625875) B5625875
theorem B7486343 : Blo 984595 7486343 := bstep (se 1 (by rfl) ⟨5614757, by rfl⟩ : syracuseStep 7486343 = 11229515) B11229515
theorem B4209565 : Blo 984595 4209565 := bstep (se 3 (by rfl) ⟨789293, by rfl⟩ : syracuseStep 4209565 = 1578587) B1578587
theorem B3324887 : Blo 984595 3324887 := bstep (se 1 (by rfl) ⟨2493665, by rfl⟩ : syracuseStep 3324887 = 4987331) B4987331
theorem B51264683 : Blo 984595 51264683 := bstep (se 1 (by rfl) ⟨38448512, by rfl⟩ : syracuseStep 51264683 = 76897025) B76897025
theorem B8994017 : Blo 984595 8994017 := bstep (se 2 (by rfl) ⟨3372756, by rfl⟩ : syracuseStep 8994017 = 6745513) B6745513
theorem B3751343 : Blo 984595 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B15973985 : Blo 984595 15973985 := bstep (se 2 (by rfl) ⟨5990244, by rfl⟩ : syracuseStep 15973985 = 11980489) B11980489
theorem B5684903 : Blo 984595 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B16826777 : Blo 984595 16826777 := bstep (se 2 (by rfl) ⟨6310041, by rfl⟩ : syracuseStep 16826777 = 12620083) B12620083
theorem B3752527 : Blo 984595 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B4998185 : Blo 984595 4998185 := bstep (se 2 (by rfl) ⟨1874319, by rfl⟩ : syracuseStep 4998185 = 3748639) B3748639
theorem B5063735 : Blo 984595 5063735 := bstep (se 1 (by rfl) ⟨3797801, by rfl⟩ : syracuseStep 5063735 = 7595603) B7595603
theorem B3163967 : Blo 984595 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B9488285 : Blo 984595 9488285 := bstep (se 3 (by rfl) ⟨1779053, by rfl⟩ : syracuseStep 9488285 = 3558107) B3558107
theorem B4737145 : Blo 984595 4737145 := bstep (se 2 (by rfl) ⟨1776429, by rfl⟩ : syracuseStep 4737145 = 3552859) B3552859
theorem B12830875 : Blo 984595 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B16861769 : Blo 984595 16861769 := bstep (se 2 (by rfl) ⟨6323163, by rfl⟩ : syracuseStep 16861769 = 12646327) B12646327
theorem B3328775 : Blo 984595 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B4213565 : Blo 984595 4213565 := bstep (se 3 (by rfl) ⟨790043, by rfl⟩ : syracuseStep 4213565 = 1580087) B1580087
theorem B3165095 : Blo 984595 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B18009125 : Blo 984595 18009125 := bstep (se 4 (by rfl) ⟨1688355, by rfl⟩ : syracuseStep 18009125 = 3376711) B3376711
theorem B7490717 : Blo 984595 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B7097705 : Blo 984595 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B49270139 : Blo 984595 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B3329801 : Blo 984595 3329801 := bstep (se 2 (by rfl) ⟨1248675, by rfl⟩ : syracuseStep 3329801 = 2497351) B2497351
theorem B3329855 : Blo 984595 3329855 := bstep (se 1 (by rfl) ⟨2497391, by rfl⟩ : syracuseStep 3329855 = 4994783) B4994783
theorem B10407851 : Blo 984595 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B18927665 : Blo 984595 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B8016509 : Blo 984595 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B2216699 : Blo 984595 2216699 := bstep (se 1 (by rfl) ⟨1662524, by rfl⟩ : syracuseStep 2216699 = 3325049) B3325049
theorem B2216915 : Blo 984595 2216915 := bstep (se 1 (by rfl) ⟨1662686, by rfl⟩ : syracuseStep 2216915 = 3325373) B3325373
theorem B7099721 : Blo 984595 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B4200355277 : Blo 984595 4200355277 := bstep (se 3 (by rfl) ⟨787566614, by rfl⟩ : syracuseStep 4200355277 = 1575133229) B1575133229
theorem B2807369 : Blo 984595 2807369 := bstep (se 2 (by rfl) ⟨1052763, by rfl⟩ : syracuseStep 2807369 = 2105527) B2105527
theorem B3790921 : Blo 984595 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B5626583 : Blo 984595 5626583 := bstep (se 1 (by rfl) ⟨4219937, by rfl⟩ : syracuseStep 5626583 = 8439875) B8439875
theorem B9493357 : Blo 984595 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B1661863 : Blo 984595 1661863 := bstep (se 1 (by rfl) ⟨1246397, by rfl⟩ : syracuseStep 1661863 = 2492795) B2492795
theorem B3333095 : Blo 984595 3333095 := bstep (se 1 (by rfl) ⟨2499821, by rfl⟩ : syracuseStep 3333095 = 4999643) B4999643
theorem B2219003 : Blo 984595 2219003 := bstep (se 1 (by rfl) ⟨1664252, by rfl⟩ : syracuseStep 2219003 = 3328505) B3328505
theorem B2219219 : Blo 984595 2219219 := bstep (se 1 (by rfl) ⟨1664414, by rfl⟩ : syracuseStep 2219219 = 3328829) B3328829
theorem B1662329 : Blo 984595 1662329 := bstep (se 2 (by rfl) ⟨623373, by rfl⟩ : syracuseStep 1662329 = 1246747) B1246747
theorem B1662889 : Blo 984595 1662889 := bstep (se 2 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 1662889 = 1247167) B1247167
theorem B2219975 : Blo 984595 2219975 := bstep (se 1 (by rfl) ⟨1664981, by rfl⟩ : syracuseStep 2219975 = 3329963) B3329963
theorem B3334121 : Blo 984595 3334121 := bstep (se 2 (by rfl) ⟨1250295, by rfl⟩ : syracuseStep 3334121 = 2500591) B2500591
theorem B1663031 : Blo 984595 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B2220335 : Blo 984595 2220335 := bstep (se 1 (by rfl) ⟨1665251, by rfl⟩ : syracuseStep 2220335 = 3330503) B3330503
theorem B2220551 : Blo 984595 2220551 := bstep (se 1 (by rfl) ⟨1665413, by rfl⟩ : syracuseStep 2220551 = 3330827) B3330827
theorem B2221217 : Blo 984595 2221217 := bstep (se 2 (by rfl) ⟨832956, by rfl⟩ : syracuseStep 2221217 = 1665913) B1665913
theorem B1664543 : Blo 984595 1664543 := bstep (se 1 (by rfl) ⟨1248407, by rfl⟩ : syracuseStep 1664543 = 2496815) B2496815
theorem B2221631 : Blo 984595 2221631 := bstep (se 1 (by rfl) ⟨1666223, by rfl⟩ : syracuseStep 2221631 = 3332447) B3332447
theorem B63891017 : Blo 984595 63891017 := bstep (se 2 (by rfl) ⟨23959131, by rfl⟩ : syracuseStep 63891017 = 47918263) B47918263
theorem B1107823 : Blo 984595 1107823 := bstep (se 1 (by rfl) ⟨830867, by rfl⟩ : syracuseStep 1107823 = 1661735) B1661735
theorem B2221991 : Blo 984595 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B15984749 : Blo 984595 15984749 := bstep (se 3 (by rfl) ⟨2997140, by rfl⟩ : syracuseStep 15984749 = 5994281) B5994281
theorem B9005435 : Blo 984595 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B4221355 : Blo 984595 4221355 := bstep (se 1 (by rfl) ⟨3166016, by rfl⟩ : syracuseStep 4221355 = 6332033) B6332033
theorem B2812391 : Blo 984595 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B1665839 : Blo 984595 1665839 := bstep (se 1 (by rfl) ⟨1249379, by rfl⟩ : syracuseStep 1665839 = 2498759) B2498759
theorem B2812801 : Blo 984595 2812801 := bstep (se 2 (by rfl) ⟨1054800, by rfl⟩ : syracuseStep 2812801 = 2109601) B2109601
theorem B1666075 : Blo 984595 1666075 := bstep (se 1 (by rfl) ⟨1249556, by rfl⟩ : syracuseStep 1666075 = 2499113) B2499113
theorem B2813143 : Blo 984595 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B58354937 : Blo 984595 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B8416669 : Blo 984595 8416669 := bstep (se 3 (by rfl) ⟨1578125, by rfl⟩ : syracuseStep 8416669 = 3156251) B3156251
theorem B1896539 : Blo 984595 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B12644687 : Blo 984595 12644687 := bstep (se 1 (by rfl) ⟨9483515, by rfl⟩ : syracuseStep 12644687 = 18967031) B18967031
theorem B2814601 : Blo 984595 2814601 := bstep (se 2 (by rfl) ⟨1055475, by rfl⟩ : syracuseStep 2814601 = 2110951) B2110951
theorem B14217893 : Blo 984595 14217893 := bstep (se 4 (by rfl) ⟨1332927, by rfl⟩ : syracuseStep 14217893 = 2665855) B2665855
theorem B1667803 : Blo 984595 1667803 := bstep (se 1 (by rfl) ⟨1250852, by rfl⟩ : syracuseStep 1667803 = 2501705) B2501705
theorem B1667999 : Blo 984595 1667999 := bstep (se 1 (by rfl) ⟨1250999, by rfl⟩ : syracuseStep 1667999 = 2501999) B2501999
theorem B3994535 : Blo 984595 3994535 := bstep (se 1 (by rfl) ⟨2995901, by rfl⟩ : syracuseStep 3994535 = 5991803) B5991803
theorem B7107563 : Blo 984595 7107563 := bstep (se 1 (by rfl) ⟨5330672, by rfl⟩ : syracuseStep 7107563 = 10661345) B10661345
theorem B5338331 : Blo 984595 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B1734967 : Blo 984595 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B1899001 : Blo 984595 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B16022117 : Blo 984595 16022117 := bstep (se 4 (by rfl) ⟨1502073, by rfl⟩ : syracuseStep 16022117 = 3004147) B3004147
theorem B2849519 : Blo 984595 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B16874891 : Blo 984595 16874891 := bstep (se 1 (by rfl) ⟨12656168, by rfl⟩ : syracuseStep 16874891 = 25312337) B25312337
theorem B41090723 : Blo 984595 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B3375823 : Blo 984595 3375823 := bstep (se 1 (by rfl) ⟨2531867, by rfl⟩ : syracuseStep 3375823 = 5063735) B5063735
theorem B2163943 : Blo 984595 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B6325523 : Blo 984595 6325523 := bstep (se 1 (by rfl) ⟨4744142, by rfl⟩ : syracuseStep 6325523 = 9488285) B9488285
theorem B11241179 : Blo 984595 11241179 := bstep (se 1 (by rfl) ⟨8430884, by rfl⟩ : syracuseStep 11241179 = 16861769) B16861769
theorem B10684487 : Blo 984595 10684487 := bstep (se 1 (by rfl) ⟨8013365, by rfl⟩ : syracuseStep 10684487 = 16026731) B16026731
theorem B10652093 : Blo 984595 10652093 := bstep (se 3 (by rfl) ⟨1997267, by rfl⟩ : syracuseStep 10652093 = 3994535) B3994535
theorem B1477097 : Blo 984595 1477097 := bstep (se 2 (by rfl) ⟨553911, by rfl⟩ : syracuseStep 1477097 = 1107823) B1107823
theorem B12618443 : Blo 984595 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B1477799 : Blo 984595 1477799 := bstep (se 1 (by rfl) ⟨1108349, by rfl⟩ : syracuseStep 1477799 = 2216699) B2216699
theorem B1477943 : Blo 984595 1477943 := bstep (se 1 (by rfl) ⟨1108457, by rfl⟩ : syracuseStep 1477943 = 2216915) B2216915
theorem B986559 : Blo 984595 986559 := bstep (se 1 (by rfl) ⟨739919, by rfl⟩ : syracuseStep 986559 = 1479839) B1479839
theorem B1871579 : Blo 984595 1871579 := bstep (se 1 (by rfl) ⟨1403684, by rfl⟩ : syracuseStep 1871579 = 2807369) B2807369
theorem B986971 : Blo 984595 986971 := bstep (se 1 (by rfl) ⟨740228, by rfl⟩ : syracuseStep 986971 = 1480457) B1480457
theorem B987387 : Blo 984595 987387 := bstep (se 1 (by rfl) ⟨740540, by rfl⟩ : syracuseStep 987387 = 1481081) B1481081
theorem B2494759 : Blo 984595 2494759 := bstep (se 1 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 2494759 = 3742139) B3742139
theorem B2495033 : Blo 984595 2495033 := bstep (se 2 (by rfl) ⟨935637, by rfl⟩ : syracuseStep 2495033 = 1871275) B1871275
theorem B987739 : Blo 984595 987739 := bstep (se 1 (by rfl) ⟨740804, by rfl⟩ : syracuseStep 987739 = 1481609) B1481609
theorem B1479335 : Blo 984595 1479335 := bstep (se 1 (by rfl) ⟨1109501, by rfl⟩ : syracuseStep 1479335 = 2219003) B2219003
theorem B2495195 : Blo 984595 2495195 := bstep (se 1 (by rfl) ⟨1871396, by rfl⟩ : syracuseStep 2495195 = 3742793) B3742793
theorem B1479479 : Blo 984595 1479479 := bstep (se 1 (by rfl) ⟨1109609, by rfl⟩ : syracuseStep 1479479 = 2219219) B2219219
theorem B988095 : Blo 984595 988095 := bstep (se 1 (by rfl) ⟨741071, by rfl⟩ : syracuseStep 988095 = 1482143) B1482143
theorem B988191 : Blo 984595 988191 := bstep (se 1 (by rfl) ⟨741143, by rfl⟩ : syracuseStep 988191 = 1482287) B1482287
theorem B55579871 : Blo 984595 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B1479983 : Blo 984595 1479983 := bstep (se 1 (by rfl) ⟨1109987, by rfl⟩ : syracuseStep 1479983 = 2219975) B2219975
theorem B988543 : Blo 984595 988543 := bstep (se 1 (by rfl) ⟨741407, by rfl⟩ : syracuseStep 988543 = 1482815) B1482815
theorem B1480223 : Blo 984595 1480223 := bstep (se 1 (by rfl) ⟨1110167, by rfl⟩ : syracuseStep 1480223 = 2220335) B2220335
theorem B2496167 : Blo 984595 2496167 := bstep (se 1 (by rfl) ⟨1872125, by rfl⟩ : syracuseStep 2496167 = 3744251) B3744251
theorem B1480367 : Blo 984595 1480367 := bstep (se 1 (by rfl) ⟨1110275, by rfl⟩ : syracuseStep 1480367 = 2220551) B2220551
theorem B1251055 : Blo 984595 1251055 := bstep (se 1 (by rfl) ⟨938291, by rfl⟩ : syracuseStep 1251055 = 1876583) B1876583
theorem B2496491 : Blo 984595 2496491 := bstep (se 1 (by rfl) ⟨1872368, by rfl⟩ : syracuseStep 2496491 = 3744737) B3744737
theorem B1054715 : Blo 984595 1054715 := bstep (se 1 (by rfl) ⟨791036, by rfl⟩ : syracuseStep 1054715 = 1582073) B1582073
theorem B1480811 : Blo 984595 1480811 := bstep (se 1 (by rfl) ⟨1110608, by rfl⟩ : syracuseStep 1480811 = 2221217) B2221217
theorem B1481087 : Blo 984595 1481087 := bstep (se 1 (by rfl) ⟨1110815, by rfl⟩ : syracuseStep 1481087 = 2221631) B2221631
theorem B2497007 : Blo 984595 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B1481327 : Blo 984595 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B6003623 : Blo 984595 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B4987817 : Blo 984595 4987817 := bstep (se 2 (by rfl) ⟨1870431, by rfl⟩ : syracuseStep 4987817 = 3740863) B3740863
theorem B1874927 : Blo 984595 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B2497817 : Blo 984595 2497817 := bstep (se 2 (by rfl) ⟨936681, by rfl⟩ : syracuseStep 2497817 = 1873363) B1873363
theorem B38903291 : Blo 984595 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B2498323 : Blo 984595 2498323 := bstep (se 1 (by rfl) ⟨1873742, by rfl⟩ : syracuseStep 2498323 = 3747485) B3747485
theorem B3743567 : Blo 984595 3743567 := bstep (se 1 (by rfl) ⟨2807675, by rfl⟩ : syracuseStep 3743567 = 5615351) B5615351
theorem B5054561 : Blo 984595 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B8429791 : Blo 984595 8429791 := bstep (se 1 (by rfl) ⟨6322343, by rfl⟩ : syracuseStep 8429791 = 12644687) B12644687
theorem B2105671 : Blo 984595 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B9478595 : Blo 984595 9478595 := bstep (se 1 (by rfl) ⟨7108946, by rfl⟩ : syracuseStep 9478595 = 14217893) B14217893
theorem B2368055 : Blo 984595 2368055 := bstep (se 1 (by rfl) ⟨1776041, by rfl⟩ : syracuseStep 2368055 = 3552083) B3552083
theorem B2532001 : Blo 984595 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B12657809 : Blo 984595 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B4007087 : Blo 984595 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B5612753 : Blo 984595 5612753 := bstep (se 2 (by rfl) ⟨2104782, by rfl⟩ : syracuseStep 5612753 = 4209565) B4209565
theorem B2499943 : Blo 984595 2499943 := bstep (se 1 (by rfl) ⟨1874957, by rfl⟩ : syracuseStep 2499943 = 3749915) B3749915
theorem B4990895 : Blo 984595 4990895 := bstep (se 1 (by rfl) ⟨3743171, by rfl⟩ : syracuseStep 4990895 = 7486343) B7486343
theorem B11249927 : Blo 984595 11249927 := bstep (se 1 (by rfl) ⟨8437445, by rfl⟩ : syracuseStep 11249927 = 16874891) B16874891
theorem B2500895 : Blo 984595 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B11217851 : Blo 984595 11217851 := bstep (se 1 (by rfl) ⟨8413388, by rfl⟩ : syracuseStep 11217851 = 16826777) B16826777
theorem B2108713 : Blo 984595 2108713 := bstep (se 2 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 2108713 = 1581535) B1581535
theorem B68431333 : Blo 984595 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B20229749 : Blo 984595 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B2109311 : Blo 984595 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B10661867 : Blo 984595 10661867 := bstep (se 1 (by rfl) ⟨7996400, by rfl⟩ : syracuseStep 10661867 = 15992801) B15992801
theorem B21377357 : Blo 984595 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B2110063 : Blo 984595 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B12006083 : Blo 984595 12006083 := bstep (se 1 (by rfl) ⟨9004562, by rfl⟩ : syracuseStep 12006083 = 18009125) B18009125
theorem B4993811 : Blo 984595 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B4731803 : Blo 984595 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B32846759 : Blo 984595 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B5617127 : Blo 984595 5617127 := bstep (se 1 (by rfl) ⟨4212845, by rfl⟩ : syracuseStep 5617127 = 8425691) B8425691
theorem B3323645 : Blo 984595 3323645 := bstep (se 3 (by rfl) ⟨623183, by rfl⟩ : syracuseStep 3323645 = 1246367) B1246367
theorem B4733147 : Blo 984595 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B2800236851 : Blo 984595 2800236851 := bstep (se 1 (by rfl) ⟨2100177638, by rfl⟩ : syracuseStep 2800236851 = 4200355277) B4200355277
theorem B3750401 : Blo 984595 3750401 := bstep (se 2 (by rfl) ⟨1406400, by rfl⟩ : syracuseStep 3750401 = 2812801) B2812801
theorem B3750857 : Blo 984595 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B3751055 : Blo 984595 3751055 := bstep (se 1 (by rfl) ⟨2813291, by rfl⟩ : syracuseStep 3751055 = 5626583) B5626583
theorem B11222225 : Blo 984595 11222225 := bstep (se 2 (by rfl) ⟨4208334, by rfl⟩ : syracuseStep 11222225 = 8416669) B8416669
theorem B3325481 : Blo 984595 3325481 := bstep (se 2 (by rfl) ⟨1247055, by rfl⟩ : syracuseStep 3325481 = 2494111) B2494111
theorem B3752801 : Blo 984595 3752801 := bstep (se 2 (by rfl) ⟨1407300, by rfl⟩ : syracuseStep 3752801 = 2814601) B2814601
theorem B5620751 : Blo 984595 5620751 := bstep (se 1 (by rfl) ⟨4215563, by rfl⟩ : syracuseStep 5620751 = 8431127) B8431127
theorem B175097227 : Blo 984595 175097227 := bstep (se 1 (by rfl) ⟨131322920, by rfl⟩ : syracuseStep 175097227 = 262645841) B262645841
theorem B4213241 : Blo 984595 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B3328937 : Blo 984595 3328937 := bstep (se 2 (by rfl) ⟨1248351, by rfl⟩ : syracuseStep 3328937 = 2496703) B2496703
theorem B3328991 : Blo 984595 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B2313289 : Blo 984595 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B3329153 : Blo 984595 3329153 := bstep (se 2 (by rfl) ⟨1248432, by rfl⟩ : syracuseStep 3329153 = 2496865) B2496865
theorem B4738375 : Blo 984595 4738375 := bstep (se 1 (by rfl) ⟨3553781, by rfl⟩ : syracuseStep 4738375 = 7107563) B7107563
theorem B3558887 : Blo 984595 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B5000777 : Blo 984595 5000777 := bstep (se 2 (by rfl) ⟨1875291, by rfl⟩ : syracuseStep 5000777 = 3750583) B3750583
theorem B2215817 : Blo 984595 2215817 := bstep (se 2 (by rfl) ⟨830931, by rfl⟩ : syracuseStep 2215817 = 1661863) B1661863
theorem B2805671 : Blo 984595 2805671 := bstep (se 1 (by rfl) ⟨2104253, by rfl⟩ : syracuseStep 2805671 = 4208507) B4208507
theorem B3330665 : Blo 984595 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B2216591 : Blo 984595 2216591 := bstep (se 1 (by rfl) ⟨1662443, by rfl⟩ : syracuseStep 2216591 = 3324887) B3324887
theorem B3789935 : Blo 984595 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B2217185 : Blo 984595 2217185 := bstep (se 2 (by rfl) ⟨831444, by rfl⟩ : syracuseStep 2217185 = 1662889) B1662889
theorem B3332123 : Blo 984595 3332123 := bstep (se 1 (by rfl) ⟨2499092, by rfl⟩ : syracuseStep 3332123 = 4998185) B4998185
theorem B5003369 : Blo 984595 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B3332609 : Blo 984595 3332609 := bstep (se 2 (by rfl) ⟨1249728, by rfl⟩ : syracuseStep 3332609 = 2499457) B2499457
theorem B2219183 : Blo 984595 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B2809043 : Blo 984595 2809043 := bstep (se 1 (by rfl) ⟨2106782, by rfl⟩ : syracuseStep 2809043 = 4213565) B4213565
theorem B14245571 : Blo 984595 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B2219867 : Blo 984595 2219867 := bstep (se 1 (by rfl) ⟨1664900, by rfl⟩ : syracuseStep 2219867 = 3329801) B3329801
theorem B2219903 : Blo 984595 2219903 := bstep (se 1 (by rfl) ⟨1664927, by rfl⟩ : syracuseStep 2219903 = 3329855) B3329855
theorem B6938567 : Blo 984595 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B6316193 : Blo 984595 6316193 := bstep (se 2 (by rfl) ⟨2368572, by rfl⟩ : syracuseStep 6316193 = 4737145) B4737145
theorem B13525451 : Blo 984595 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B5628473 : Blo 984595 5628473 := bstep (se 2 (by rfl) ⟨2110677, by rfl⟩ : syracuseStep 5628473 = 4221355) B4221355
theorem B19195193 : Blo 984595 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B2221433 : Blo 984595 2221433 := bstep (se 2 (by rfl) ⟨833037, by rfl⟩ : syracuseStep 2221433 = 1666075) B1666075
theorem B1402363 : Blo 984595 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B1402471 : Blo 984595 1402471 := bstep (se 1 (by rfl) ⟨1051853, by rfl⟩ : syracuseStep 1402471 = 2103707) B2103707
theorem B2222063 : Blo 984595 2222063 := bstep (se 1 (by rfl) ⟨1666547, by rfl⟩ : syracuseStep 2222063 = 3333095) B3333095
theorem B1108219 : Blo 984595 1108219 := bstep (se 1 (by rfl) ⟨831164, by rfl⟩ : syracuseStep 1108219 = 1662329) B1662329
theorem B21326327 : Blo 984595 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B2222747 : Blo 984595 2222747 := bstep (se 1 (by rfl) ⟨1667060, by rfl⟩ : syracuseStep 2222747 = 3334121) B3334121
theorem B1108687 : Blo 984595 1108687 := bstep (se 1 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 1108687 = 1663031) B1663031
theorem B42625997 : Blo 984595 42625997 := bstep (se 3 (by rfl) ⟨7992374, by rfl⟩ : syracuseStep 42625997 = 15984749) B15984749
theorem B7204069 : Blo 984595 7204069 := bstep (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) B1350763
theorem B2223737 : Blo 984595 2223737 := bstep (se 2 (by rfl) ⟨833901, by rfl⟩ : syracuseStep 2223737 = 1667803) B1667803
theorem B1109695 : Blo 984595 1109695 := bstep (se 1 (by rfl) ⟨832271, by rfl⟩ : syracuseStep 1109695 = 1664543) B1664543
theorem B42594011 : Blo 984595 42594011 := bstep (se 1 (by rfl) ⟨31945508, by rfl⟩ : syracuseStep 42594011 = 63891017) B63891017
theorem B2814077 : Blo 984595 2814077 := bstep (se 3 (by rfl) ⟨527639, by rfl⟩ : syracuseStep 2814077 = 1055279) B1055279
theorem B1110559 : Blo 984595 1110559 := bstep (se 1 (by rfl) ⟨832919, by rfl⟩ : syracuseStep 1110559 = 1665839) B1665839
theorem B7598717 : Blo 984595 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B1668127 : Blo 984595 1668127 := bstep (se 1 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 1668127 = 2502191) B2502191
theorem B23984045 : Blo 984595 23984045 := bstep (se 3 (by rfl) ⟨4497008, by rfl⟩ : syracuseStep 23984045 = 8994017) B8994017
theorem B1111999 : Blo 984595 1111999 := bstep (se 1 (by rfl) ⟨833999, by rfl⟩ : syracuseStep 1111999 = 1667999) B1667999
theorem B10681411 : Blo 984595 10681411 := bstep (se 1 (by rfl) ⟨8011058, by rfl⟩ : syracuseStep 10681411 = 16022117) B16022117
theorem B34176455 : Blo 984595 34176455 := bstep (se 1 (by rfl) ⟨25632341, by rfl⟩ : syracuseStep 34176455 = 51264683) B51264683
theorem B10649323 : Blo 984595 10649323 := bstep (se 1 (by rfl) ⟨7986992, by rfl⟩ : syracuseStep 10649323 = 15973985) B15973985
theorem B27393815 : Blo 984595 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B11239721 : Blo 984595 11239721 := bstep (se 2 (by rfl) ⟨4214895, by rfl⟩ : syracuseStep 11239721 = 8429791) B8429791
theorem B3376001 : Blo 984595 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B2885257 : Blo 984595 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B984731 : Blo 984595 984731 := bstep (se 1 (by rfl) ⟨738548, by rfl⟩ : syracuseStep 984731 = 1477097) B1477097
theorem B1869817 : Blo 984595 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B985199 : Blo 984595 985199 := bstep (se 1 (by rfl) ⟨738899, by rfl⟩ : syracuseStep 985199 = 1477799) B1477799
theorem B1869961 : Blo 984595 1869961 := bstep (se 2 (by rfl) ⟨701235, by rfl⟩ : syracuseStep 1869961 = 1402471) B1402471
theorem B985295 : Blo 984595 985295 := bstep (se 1 (by rfl) ⟨738971, by rfl⟩ : syracuseStep 985295 = 1477943) B1477943
theorem B1247719 : Blo 984595 1247719 := bstep (se 1 (by rfl) ⟨935789, by rfl⟩ : syracuseStep 1247719 = 1871579) B1871579
theorem B1477211 : Blo 984595 1477211 := bstep (se 1 (by rfl) ⟨1107908, by rfl⟩ : syracuseStep 1477211 = 2215817) B2215817
theorem B1870447 : Blo 984595 1870447 := bstep (se 1 (by rfl) ⟨1402835, by rfl⟩ : syracuseStep 1870447 = 2805671) B2805671
theorem B1477625 : Blo 984595 1477625 := bstep (se 2 (by rfl) ⟨554109, by rfl⟩ : syracuseStep 1477625 = 1108219) B1108219
theorem B1477727 : Blo 984595 1477727 := bstep (se 1 (by rfl) ⟨1108295, by rfl⟩ : syracuseStep 1477727 = 2216591) B2216591
theorem B986223 : Blo 984595 986223 := bstep (se 1 (by rfl) ⟨739667, by rfl⟩ : syracuseStep 986223 = 1479335) B1479335
theorem B986319 : Blo 984595 986319 := bstep (se 1 (by rfl) ⟨739739, by rfl⟩ : syracuseStep 986319 = 1479479) B1479479
theorem B2526623 : Blo 984595 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B1478123 : Blo 984595 1478123 := bstep (se 1 (by rfl) ⟨1108592, by rfl⟩ : syracuseStep 1478123 = 2217185) B2217185
theorem B986655 : Blo 984595 986655 := bstep (se 1 (by rfl) ⟨739991, by rfl⟩ : syracuseStep 986655 = 1479983) B1479983
theorem B1478249 : Blo 984595 1478249 := bstep (se 2 (by rfl) ⟨554343, by rfl⟩ : syracuseStep 1478249 = 1108687) B1108687
theorem B986815 : Blo 984595 986815 := bstep (se 1 (by rfl) ⟨740111, by rfl⟩ : syracuseStep 986815 = 1480223) B1480223
theorem B986911 : Blo 984595 986911 := bstep (se 1 (by rfl) ⟨740183, by rfl⟩ : syracuseStep 986911 = 1480367) B1480367
theorem B987207 : Blo 984595 987207 := bstep (se 1 (by rfl) ⟨740405, by rfl⟩ : syracuseStep 987207 = 1480811) B1480811
theorem B987391 : Blo 984595 987391 := bstep (se 1 (by rfl) ⟨740543, by rfl⟩ : syracuseStep 987391 = 1481087) B1481087
theorem B9605425 : Blo 984595 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B987551 : Blo 984595 987551 := bstep (se 1 (by rfl) ⟨740663, by rfl⟩ : syracuseStep 987551 = 1481327) B1481327
theorem B4002415 : Blo 984595 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B1479455 : Blo 984595 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1872695 : Blo 984595 1872695 := bstep (se 1 (by rfl) ⟨1404521, by rfl⟩ : syracuseStep 1872695 = 2809043) B2809043
theorem B1479593 : Blo 984595 1479593 := bstep (se 2 (by rfl) ⟨554847, by rfl⟩ : syracuseStep 1479593 = 1109695) B1109695
theorem B2495711 : Blo 984595 2495711 := bstep (se 1 (by rfl) ⟨1871783, by rfl⟩ : syracuseStep 2495711 = 3743567) B3743567
theorem B1479911 : Blo 984595 1479911 := bstep (se 1 (by rfl) ⟨1109933, by rfl⟩ : syracuseStep 1479911 = 2219867) B2219867
theorem B1479935 : Blo 984595 1479935 := bstep (se 1 (by rfl) ⟨1109951, by rfl⟩ : syracuseStep 1479935 = 2219903) B2219903
theorem B4625711 : Blo 984595 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B9016967 : Blo 984595 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B1578703 : Blo 984595 1578703 := bstep (se 1 (by rfl) ⟨1184027, by rfl⟩ : syracuseStep 1578703 = 2368055) B2368055
theorem B1480745 : Blo 984595 1480745 := bstep (se 2 (by rfl) ⟨555279, by rfl⟩ : syracuseStep 1480745 = 1110559) B1110559
theorem B3741835 : Blo 984595 3741835 := bstep (se 1 (by rfl) ⟨2806376, by rfl⟩ : syracuseStep 3741835 = 5612753) B5612753
theorem B1480955 : Blo 984595 1480955 := bstep (se 1 (by rfl) ⟨1110716, by rfl⟩ : syracuseStep 1480955 = 2221433) B2221433
theorem B1481375 : Blo 984595 1481375 := bstep (se 1 (by rfl) ⟨1111031, by rfl⟩ : syracuseStep 1481375 = 2222063) B2222063
theorem B1481831 : Blo 984595 1481831 := bstep (se 1 (by rfl) ⟨1111373, by rfl⟩ : syracuseStep 1481831 = 2222747) B2222747
theorem B7478567 : Blo 984595 7478567 := bstep (se 1 (by rfl) ⟨5608925, by rfl⟩ : syracuseStep 7478567 = 11217851) B11217851
theorem B28417331 : Blo 984595 28417331 := bstep (se 1 (by rfl) ⟨21312998, by rfl⟩ : syracuseStep 28417331 = 42625997) B42625997
theorem B1482491 : Blo 984595 1482491 := bstep (se 1 (by rfl) ⟨1111868, by rfl⟩ : syracuseStep 1482491 = 2223737) B2223737
theorem B1482665 : Blo 984595 1482665 := bstep (se 2 (by rfl) ⟨555999, by rfl⟩ : syracuseStep 1482665 = 1111999) B1111999
theorem B1876051 : Blo 984595 1876051 := bstep (se 1 (by rfl) ⟨1407038, by rfl⟩ : syracuseStep 1876051 = 2814077) B2814077
theorem B8004055 : Blo 984595 8004055 := bstep (se 1 (by rfl) ⟨6003041, by rfl⟩ : syracuseStep 8004055 = 12006083) B12006083
theorem B3154535 : Blo 984595 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B21897839 : Blo 984595 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B3744751 : Blo 984595 3744751 := bstep (se 1 (by rfl) ⟨2808563, by rfl⟩ : syracuseStep 3744751 = 5617127) B5617127
theorem B3155431 : Blo 984595 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B2500267 : Blo 984595 2500267 := bstep (se 1 (by rfl) ⟨1875200, by rfl⟩ : syracuseStep 2500267 = 3750401) B3750401
theorem B37988189 : Blo 984595 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B2500571 : Blo 984595 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B2500703 : Blo 984595 2500703 := bstep (se 1 (by rfl) ⟨1875527, by rfl⟩ : syracuseStep 2500703 = 3751055) B3751055
theorem B7481483 : Blo 984595 7481483 := bstep (se 1 (by rfl) ⟨5611112, by rfl⟩ : syracuseStep 7481483 = 11222225) B11222225
theorem B22784303 : Blo 984595 22784303 := bstep (se 1 (by rfl) ⟨17088227, by rfl⟩ : syracuseStep 22784303 = 34176455) B34176455
theorem B14199097 : Blo 984595 14199097 := bstep (se 2 (by rfl) ⟨5324661, by rfl⟩ : syracuseStep 14199097 = 10649323) B10649323
theorem B18262543 : Blo 984595 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B2501867 : Blo 984595 2501867 := bstep (se 1 (by rfl) ⟨1876400, by rfl⟩ : syracuseStep 2501867 = 3752801) B3752801
theorem B3747167 : Blo 984595 3747167 := bstep (se 1 (by rfl) ⟨2810375, by rfl⟩ : syracuseStep 3747167 = 5620751) B5620751
theorem B4501097 : Blo 984595 4501097 := bstep (se 2 (by rfl) ⟨1687911, by rfl⟩ : syracuseStep 4501097 = 3375823) B3375823
theorem B7122991 : Blo 984595 7122991 := bstep (se 1 (by rfl) ⟨5342243, by rfl⟩ : syracuseStep 7122991 = 10684487) B10684487
theorem B2372591 : Blo 984595 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B3325211 : Blo 984595 3325211 := bstep (se 1 (by rfl) ⟨2493908, by rfl⟩ : syracuseStep 3325211 = 4987817) B4987817
theorem B91241777 : Blo 984595 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B25935527 : Blo 984595 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B4210795 : Blo 984595 4210795 := bstep (se 1 (by rfl) ⟨3158096, by rfl⟩ : syracuseStep 4210795 = 6316193) B6316193
theorem B3752315 : Blo 984595 3752315 := bstep (se 1 (by rfl) ⟨2814236, by rfl⟩ : syracuseStep 3752315 = 5628473) B5628473
theorem B12337541 : Blo 984595 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B3326345 : Blo 984595 3326345 := bstep (se 2 (by rfl) ⟨1247379, by rfl⟩ : syracuseStep 3326345 = 2494759) B2494759
theorem B8438539 : Blo 984595 8438539 := bstep (se 1 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 8438539 = 12657809) B12657809
theorem B2671391 : Blo 984595 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B12796795 : Blo 984595 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B3327263 : Blo 984595 3327263 := bstep (se 1 (by rfl) ⟨2495447, by rfl⟩ : syracuseStep 3327263 = 4990895) B4990895
theorem B13486499 : Blo 984595 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B28396007 : Blo 984595 28396007 := bstep (se 1 (by rfl) ⟨21297005, by rfl⟩ : syracuseStep 28396007 = 42594011) B42594011
theorem B4999805 : Blo 984595 4999805 := bstep (se 3 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 4999805 = 1874927) B1874927
theorem B5065811 : Blo 984595 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B3329207 : Blo 984595 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B2215763 : Blo 984595 2215763 := bstep (se 1 (by rfl) ⟨1661822, by rfl⟩ : syracuseStep 2215763 = 3323645) B3323645
theorem B14241881 : Blo 984595 14241881 := bstep (se 2 (by rfl) ⟨5340705, by rfl⟩ : syracuseStep 14241881 = 10681411) B10681411
theorem B3331097 : Blo 984595 3331097 := bstep (se 2 (by rfl) ⟨1249161, by rfl⟩ : syracuseStep 3331097 = 2498323) B2498323
theorem B2216987 : Blo 984595 2216987 := bstep (se 1 (by rfl) ⟨1662740, by rfl⟩ : syracuseStep 2216987 = 3325481) B3325481
theorem B2807561 : Blo 984595 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B4217015 : Blo 984595 4217015 := bstep (se 1 (by rfl) ⟨3162761, by rfl⟩ : syracuseStep 4217015 = 6325523) B6325523
theorem B7494119 : Blo 984595 7494119 := bstep (se 1 (by rfl) ⟨5620589, by rfl⟩ : syracuseStep 7494119 = 11241179) B11241179
theorem B7101395 : Blo 984595 7101395 := bstep (se 1 (by rfl) ⟨5326046, by rfl⟩ : syracuseStep 7101395 = 10652093) B10652093
theorem B2808827 : Blo 984595 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B8412295 : Blo 984595 8412295 := bstep (se 1 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 8412295 = 12618443) B12618443
theorem B3333257 : Blo 984595 3333257 := bstep (se 2 (by rfl) ⟨1249971, by rfl⟩ : syracuseStep 3333257 = 2499943) B2499943
theorem B233462969 : Blo 984595 233462969 := bstep (se 2 (by rfl) ⟨87548613, by rfl⟩ : syracuseStep 233462969 = 175097227) B175097227
theorem B2219291 : Blo 984595 2219291 := bstep (se 1 (by rfl) ⟨1664468, by rfl⟩ : syracuseStep 2219291 = 3328937) B3328937
theorem B2219327 : Blo 984595 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B2219435 : Blo 984595 2219435 := bstep (se 1 (by rfl) ⟨1664576, by rfl⟩ : syracuseStep 2219435 = 3329153) B3329153
theorem B3333851 : Blo 984595 3333851 := bstep (se 1 (by rfl) ⟨2500388, by rfl⟩ : syracuseStep 3333851 = 5000777) B5000777
theorem B1663355 : Blo 984595 1663355 := bstep (se 1 (by rfl) ⟨1247516, by rfl⟩ : syracuseStep 1663355 = 2495033) B2495033
theorem B2220443 : Blo 984595 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B1663463 : Blo 984595 1663463 := bstep (se 1 (by rfl) ⟨1247597, by rfl⟩ : syracuseStep 1663463 = 2495195) B2495195
theorem B37053247 : Blo 984595 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B1664111 : Blo 984595 1664111 := bstep (se 1 (by rfl) ⟨1248083, by rfl⟩ : syracuseStep 1664111 = 2496167) B2496167
theorem B1664327 : Blo 984595 1664327 := bstep (se 1 (by rfl) ⟨1248245, by rfl⟩ : syracuseStep 1664327 = 2496491) B2496491
theorem B2221415 : Blo 984595 2221415 := bstep (se 1 (by rfl) ⟨1666061, by rfl⟩ : syracuseStep 2221415 = 3332123) B3332123
theorem B3335579 : Blo 984595 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B1664671 : Blo 984595 1664671 := bstep (se 1 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 1664671 = 2497007) B2497007
theorem B2221739 : Blo 984595 2221739 := bstep (se 1 (by rfl) ⟨1666304, by rfl⟩ : syracuseStep 2221739 = 3332609) B3332609
theorem B2811617 : Blo 984595 2811617 := bstep (se 2 (by rfl) ⟨1054356, by rfl⟩ : syracuseStep 2811617 = 2108713) B2108713
theorem B6317833 : Blo 984595 6317833 := bstep (se 2 (by rfl) ⟨2369187, by rfl⟩ : syracuseStep 6317833 = 4738375) B4738375
theorem B1665211 : Blo 984595 1665211 := bstep (se 1 (by rfl) ⟨1248908, by rfl⟩ : syracuseStep 1665211 = 2497817) B2497817
theorem B2812573 : Blo 984595 2812573 := bstep (se 3 (by rfl) ⟨527357, by rfl⟩ : syracuseStep 2812573 = 1054715) B1054715
theorem B3369707 : Blo 984595 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B6319063 : Blo 984595 6319063 := bstep (se 1 (by rfl) ⟨4739297, by rfl⟩ : syracuseStep 6319063 = 9478595) B9478595
theorem B2813417 : Blo 984595 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B2224169 : Blo 984595 2224169 := bstep (se 2 (by rfl) ⟨834063, by rfl⟩ : syracuseStep 2224169 = 1668127) B1668127
theorem B7499951 : Blo 984595 7499951 := bstep (se 1 (by rfl) ⟨5624963, by rfl⟩ : syracuseStep 7499951 = 11249927) B11249927
theorem B1667263 : Blo 984595 1667263 := bstep (se 1 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 1667263 = 2500895) B2500895
theorem B14217551 : Blo 984595 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B1668073 : Blo 984595 1668073 := bstep (se 2 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 1668073 = 1251055) B1251055
theorem B1406207 : Blo 984595 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B7107911 : Blo 984595 7107911 := bstep (se 1 (by rfl) ⟨5330933, by rfl⟩ : syracuseStep 7107911 = 10661867) B10661867
theorem B14251571 : Blo 984595 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B15989363 : Blo 984595 15989363 := bstep (se 1 (by rfl) ⟨11992022, by rfl⟩ : syracuseStep 15989363 = 23984045) B23984045
theorem B1866824567 : Blo 984595 1866824567 := bstep (se 1 (by rfl) ⟨1400118425, by rfl⟩ : syracuseStep 1866824567 = 2800236851) B2800236851
theorem B8225027 : Blo 984595 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B984807 : Blo 984595 984807 := bstep (se 1 (by rfl) ⟨738605, by rfl⟩ : syracuseStep 984807 = 1477211) B1477211
theorem B985083 : Blo 984595 985083 := bstep (se 1 (by rfl) ⟨738812, by rfl⟩ : syracuseStep 985083 = 1477625) B1477625
theorem B3377207 : Blo 984595 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B985151 : Blo 984595 985151 := bstep (se 1 (by rfl) ⟨738863, by rfl⟩ : syracuseStep 985151 = 1477727) B1477727
theorem B985415 : Blo 984595 985415 := bstep (se 1 (by rfl) ⟨739061, by rfl⟩ : syracuseStep 985415 = 1478123) B1478123
theorem B8423777 : Blo 984595 8423777 := bstep (se 2 (by rfl) ⟨3158916, by rfl⟩ : syracuseStep 8423777 = 6317833) B6317833
theorem B985499 : Blo 984595 985499 := bstep (se 1 (by rfl) ⟨739124, by rfl⟩ : syracuseStep 985499 = 1478249) B1478249
theorem B1477175 : Blo 984595 1477175 := bstep (se 1 (by rfl) ⟨1107881, by rfl⟩ : syracuseStep 1477175 = 2215763) B2215763
theorem B6326909 : Blo 984595 6326909 := bstep (se 3 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 6326909 = 2372591) B2372591
theorem B2493089 : Blo 984595 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B2493281 : Blo 984595 2493281 := bstep (se 2 (by rfl) ⟨934980, by rfl⟩ : syracuseStep 2493281 = 1869961) B1869961
theorem B986303 : Blo 984595 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B1248463 : Blo 984595 1248463 := bstep (se 1 (by rfl) ⟨936347, by rfl⟩ : syracuseStep 1248463 = 1872695) B1872695
theorem B986395 : Blo 984595 986395 := bstep (se 1 (by rfl) ⟨739796, by rfl⟩ : syracuseStep 986395 = 1479593) B1479593
theorem B1477991 : Blo 984595 1477991 := bstep (se 1 (by rfl) ⟨1108493, by rfl⟩ : syracuseStep 1477991 = 2216987) B2216987
theorem B24350057 : Blo 984595 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B2493929 : Blo 984595 2493929 := bstep (se 2 (by rfl) ⟨935223, by rfl⟩ : syracuseStep 2493929 = 1870447) B1870447
theorem B986607 : Blo 984595 986607 := bstep (se 1 (by rfl) ⟨739955, by rfl⟩ : syracuseStep 986607 = 1479911) B1479911
theorem B986623 : Blo 984595 986623 := bstep (se 1 (by rfl) ⟨739967, by rfl⟩ : syracuseStep 986623 = 1479935) B1479935
theorem B3083807 : Blo 984595 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B8425417 : Blo 984595 8425417 := bstep (se 2 (by rfl) ⟨3159531, by rfl⟩ : syracuseStep 8425417 = 6319063) B6319063
theorem B987163 : Blo 984595 987163 := bstep (se 1 (by rfl) ⟨740372, by rfl⟩ : syracuseStep 987163 = 1480745) B1480745
theorem B987303 : Blo 984595 987303 := bstep (se 1 (by rfl) ⟨740477, by rfl⟩ : syracuseStep 987303 = 1480955) B1480955
theorem B987583 : Blo 984595 987583 := bstep (se 1 (by rfl) ⟨740687, by rfl⟩ : syracuseStep 987583 = 1481375) B1481375
theorem B1872551 : Blo 984595 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B987887 : Blo 984595 987887 := bstep (se 1 (by rfl) ⟨740915, by rfl⟩ : syracuseStep 987887 = 1481831) B1481831
theorem B1479527 : Blo 984595 1479527 := bstep (se 1 (by rfl) ⟨1109645, by rfl⟩ : syracuseStep 1479527 = 2219291) B2219291
theorem B4985711 : Blo 984595 4985711 := bstep (se 1 (by rfl) ⟨3739283, by rfl⟩ : syracuseStep 4985711 = 7478567) B7478567
theorem B18944887 : Blo 984595 18944887 := bstep (se 1 (by rfl) ⟨14208665, by rfl⟩ : syracuseStep 18944887 = 28417331) B28417331
theorem B1479551 : Blo 984595 1479551 := bstep (se 1 (by rfl) ⟨1109663, by rfl⟩ : syracuseStep 1479551 = 2219327) B2219327
theorem B1479623 : Blo 984595 1479623 := bstep (se 1 (by rfl) ⟨1109717, by rfl⟩ : syracuseStep 1479623 = 2219435) B2219435
theorem B988327 : Blo 984595 988327 := bstep (se 1 (by rfl) ⟨741245, by rfl⟩ : syracuseStep 988327 = 1482491) B1482491
theorem B988443 : Blo 984595 988443 := bstep (se 1 (by rfl) ⟨741332, by rfl⟩ : syracuseStep 988443 = 1482665) B1482665
theorem B1480295 : Blo 984595 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B2103023 : Blo 984595 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B1480943 : Blo 984595 1480943 := bstep (se 1 (by rfl) ⟨1110707, by rfl⟩ : syracuseStep 1480943 = 2221415) B2221415
theorem B1481159 : Blo 984595 1481159 := bstep (se 1 (by rfl) ⟨1110869, by rfl⟩ : syracuseStep 1481159 = 2221739) B2221739
theorem B1874411 : Blo 984595 1874411 := bstep (se 1 (by rfl) ⟨1405808, by rfl⟩ : syracuseStep 1874411 = 2811617) B2811617
theorem B4987655 : Blo 984595 4987655 := bstep (se 1 (by rfl) ⟨3740741, by rfl⟩ : syracuseStep 4987655 = 7481483) B7481483
theorem B2498111 : Blo 984595 2498111 := bstep (se 1 (by rfl) ⟨1873583, by rfl⟩ : syracuseStep 2498111 = 3747167) B3747167
theorem B2104937 : Blo 984595 2104937 := bstep (se 2 (by rfl) ⟨789351, by rfl⟩ : syracuseStep 2104937 = 1578703) B1578703
theorem B1875611 : Blo 984595 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B1482779 : Blo 984595 1482779 := bstep (se 1 (by rfl) ⟨1112084, by rfl⟩ : syracuseStep 1482779 = 2224169) B2224169
theorem B4989113 : Blo 984595 4989113 := bstep (se 2 (by rfl) ⟨1870917, by rfl⟩ : syracuseStep 4989113 = 3741835) B3741835
theorem B9478367 : Blo 984595 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B11216393 : Blo 984595 11216393 := bstep (se 2 (by rfl) ⟨4206147, by rfl⟩ : syracuseStep 11216393 = 8412295) B8412295
theorem B10659575 : Blo 984595 10659575 := bstep (se 1 (by rfl) ⟨7994681, by rfl⟩ : syracuseStep 10659575 = 15989363) B15989363
theorem B60827851 : Blo 984595 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B2501401 : Blo 984595 2501401 := bstep (se 2 (by rfl) ⟨938025, by rfl⟩ : syracuseStep 2501401 = 1876051) B1876051
theorem B5614393 : Blo 984595 5614393 := bstep (se 2 (by rfl) ⟨2105397, by rfl⟩ : syracuseStep 5614393 = 4210795) B4210795
theorem B2501543 : Blo 984595 2501543 := bstep (se 1 (by rfl) ⟨1876157, by rfl⟩ : syracuseStep 2501543 = 3752315) B3752315
theorem B11251385 : Blo 984595 11251385 := bstep (se 2 (by rfl) ⟨4219269, by rfl⟩ : syracuseStep 11251385 = 8438539) B8438539
theorem B4993001 : Blo 984595 4993001 := bstep (se 2 (by rfl) ⟨1872375, by rfl⟩ : syracuseStep 4993001 = 3744751) B3744751
theorem B8990999 : Blo 984595 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B4207241 : Blo 984595 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B7123709 : Blo 984595 7123709 := bstep (se 3 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 7123709 = 2671391) B2671391
theorem B3847009 : Blo 984595 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B1684415 : Blo 984595 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B3749885 : Blo 984595 3749885 := bstep (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) B1406207
theorem B3750097 : Blo 984595 3750097 := bstep (se 2 (by rfl) ⟨1406286, by rfl⟩ : syracuseStep 3750097 = 2812573) B2812573
theorem B4996079 : Blo 984595 4996079 := bstep (se 1 (by rfl) ⟨3747059, by rfl⟩ : syracuseStep 4996079 = 7494119) B7494119
theorem B4734263 : Blo 984595 4734263 := bstep (se 1 (by rfl) ⟨3550697, by rfl⟩ : syracuseStep 4734263 = 7101395) B7101395
theorem B7486829 : Blo 984595 7486829 := bstep (se 3 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 7486829 = 2807561) B2807561
theorem B14598559 : Blo 984595 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B15189535 : Blo 984595 15189535 := bstep (se 1 (by rfl) ⟨11392151, by rfl⟩ : syracuseStep 15189535 = 22784303) B22784303
theorem B2246471 : Blo 984595 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B3000731 : Blo 984595 3000731 := bstep (se 1 (by rfl) ⟨2250548, by rfl⟩ : syracuseStep 3000731 = 4501097) B4501097
theorem B4999967 : Blo 984595 4999967 := bstep (se 1 (by rfl) ⟨3749975, by rfl⟩ : syracuseStep 4999967 = 7499951) B7499951
theorem B4738607 : Blo 984595 4738607 := bstep (se 1 (by rfl) ⟨3553955, by rfl⟩ : syracuseStep 4738607 = 7107911) B7107911
theorem B1244549711 : Blo 984595 1244549711 := bstep (se 1 (by rfl) ⟨933412283, by rfl⟩ : syracuseStep 1244549711 = 1866824567) B1866824567
theorem B2216807 : Blo 984595 2216807 := bstep (se 1 (by rfl) ⟨1662605, by rfl⟩ : syracuseStep 2216807 = 3325211) B3325211
theorem B17290351 : Blo 984595 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B7493147 : Blo 984595 7493147 := bstep (se 1 (by rfl) ⟨5619860, by rfl⟩ : syracuseStep 7493147 = 11239721) B11239721
theorem B2217563 : Blo 984595 2217563 := bstep (se 1 (by rfl) ⟨1663172, by rfl⟩ : syracuseStep 2217563 = 3326345) B3326345
theorem B2250667 : Blo 984595 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B10672073 : Blo 984595 10672073 := bstep (se 2 (by rfl) ⟨4002027, by rfl⟩ : syracuseStep 10672073 = 8004055) B8004055
theorem B2218175 : Blo 984595 2218175 := bstep (se 1 (by rfl) ⟨1663631, by rfl⟩ : syracuseStep 2218175 = 3327263) B3327263
theorem B49404329 : Blo 984595 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B18930671 : Blo 984595 18930671 := bstep (se 1 (by rfl) ⟨14198003, by rfl⟩ : syracuseStep 18930671 = 28396007) B28396007
theorem B3333203 : Blo 984595 3333203 := bstep (se 1 (by rfl) ⟨2499902, by rfl⟩ : syracuseStep 3333203 = 4999805) B4999805
theorem B2219471 : Blo 984595 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B2219561 : Blo 984595 2219561 := bstep (se 2 (by rfl) ⟨832335, by rfl⟩ : syracuseStep 2219561 = 1664671) B1664671
theorem B3333689 : Blo 984595 3333689 := bstep (se 2 (by rfl) ⟨1250133, by rfl⟩ : syracuseStep 3333689 = 2500267) B2500267
theorem B85384853 : Blo 984595 85384853 := bstep (se 6 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 85384853 = 4002415) B4002415
theorem B9494587 : Blo 984595 9494587 := bstep (se 1 (by rfl) ⟨7120940, by rfl⟩ : syracuseStep 9494587 = 14241881) B14241881
theorem B2220281 : Blo 984595 2220281 := bstep (se 2 (by rfl) ⟨832605, by rfl⟩ : syracuseStep 2220281 = 1665211) B1665211
theorem B18932129 : Blo 984595 18932129 := bstep (se 2 (by rfl) ⟨7099548, by rfl⟩ : syracuseStep 18932129 = 14199097) B14199097
theorem B1663625 : Blo 984595 1663625 := bstep (se 2 (by rfl) ⟨623859, by rfl⟩ : syracuseStep 1663625 = 1247719) B1247719
theorem B2220731 : Blo 984595 2220731 := bstep (se 1 (by rfl) ⟨1665548, by rfl⟩ : syracuseStep 2220731 = 3331097) B3331097
theorem B1663807 : Blo 984595 1663807 := bstep (se 1 (by rfl) ⟨1247855, by rfl⟩ : syracuseStep 1663807 = 2495711) B2495711
theorem B2811343 : Blo 984595 2811343 := bstep (se 1 (by rfl) ⟨2108507, by rfl⟩ : syracuseStep 2811343 = 4217015) B4217015
theorem B24045245 : Blo 984595 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B68249573 : Blo 984595 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B2222171 : Blo 984595 2222171 := bstep (se 1 (by rfl) ⟨1666628, by rfl⟩ : syracuseStep 2222171 = 3333257) B3333257
theorem B155641979 : Blo 984595 155641979 := bstep (se 1 (by rfl) ⟨116731484, by rfl⟩ : syracuseStep 155641979 = 233462969) B233462969
theorem B2222567 : Blo 984595 2222567 := bstep (se 1 (by rfl) ⟨1666925, by rfl⟩ : syracuseStep 2222567 = 3333851) B3333851
theorem B9497321 : Blo 984595 9497321 := bstep (se 2 (by rfl) ⟨3561495, by rfl⟩ : syracuseStep 9497321 = 7122991) B7122991
theorem B1108903 : Blo 984595 1108903 := bstep (se 1 (by rfl) ⟨831677, by rfl⟩ : syracuseStep 1108903 = 1663355) B1663355
theorem B2223017 : Blo 984595 2223017 := bstep (se 2 (by rfl) ⟨833631, by rfl⟩ : syracuseStep 2223017 = 1667263) B1667263
theorem B1108975 : Blo 984595 1108975 := bstep (se 1 (by rfl) ⟨831731, by rfl⟩ : syracuseStep 1108975 = 1663463) B1663463
theorem B12807233 : Blo 984595 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B1109407 : Blo 984595 1109407 := bstep (se 1 (by rfl) ⟨832055, by rfl⟩ : syracuseStep 1109407 = 1664111) B1664111
theorem B1109551 : Blo 984595 1109551 := bstep (se 1 (by rfl) ⟨832163, by rfl⟩ : syracuseStep 1109551 = 1664327) B1664327
theorem B2223719 : Blo 984595 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B25325459 : Blo 984595 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B2224097 : Blo 984595 2224097 := bstep (se 2 (by rfl) ⟨834036, by rfl⟩ : syracuseStep 2224097 = 1668073) B1668073
theorem B1667047 : Blo 984595 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B1667135 : Blo 984595 1667135 := bstep (se 1 (by rfl) ⟨1250351, by rfl⟩ : syracuseStep 1667135 = 2500703) B2500703
theorem B1667911 : Blo 984595 1667911 := bstep (se 1 (by rfl) ⟨1250933, by rfl⟩ : syracuseStep 1667911 = 2501867) B2501867
theorem B9501047 : Blo 984595 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B19464745 : Blo 984595 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B984783 : Blo 984595 984783 := bstep (se 1 (by rfl) ⟨738587, by rfl⟩ : syracuseStep 984783 = 1477175) B1477175
theorem B985327 : Blo 984595 985327 := bstep (se 1 (by rfl) ⟨738995, by rfl⟩ : syracuseStep 985327 = 1477991) B1477991
theorem B4491773 : Blo 984595 4491773 := bstep (se 3 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 4491773 = 1684415) B1684415
theorem B81103801 : Blo 984595 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B1248367 : Blo 984595 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B1477871 : Blo 984595 1477871 := bstep (se 1 (by rfl) ⟨1108403, by rfl⟩ : syracuseStep 1477871 = 2216807) B2216807
theorem B986351 : Blo 984595 986351 := bstep (se 1 (by rfl) ⟨739763, by rfl⟩ : syracuseStep 986351 = 1479527) B1479527
theorem B986367 : Blo 984595 986367 := bstep (se 1 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 986367 = 1479551) B1479551
theorem B986415 : Blo 984595 986415 := bstep (se 1 (by rfl) ⟨739811, by rfl⟩ : syracuseStep 986415 = 1479623) B1479623
theorem B1478375 : Blo 984595 1478375 := bstep (se 1 (by rfl) ⟨1108781, by rfl⟩ : syracuseStep 1478375 = 2217563) B2217563
theorem B986863 : Blo 984595 986863 := bstep (se 1 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 986863 = 1480295) B1480295
theorem B1478537 : Blo 984595 1478537 := bstep (se 2 (by rfl) ⟨554451, by rfl⟩ : syracuseStep 1478537 = 1108903) B1108903
theorem B7114715 : Blo 984595 7114715 := bstep (se 1 (by rfl) ⟨5336036, by rfl⟩ : syracuseStep 7114715 = 10672073) B10672073
theorem B1478633 : Blo 984595 1478633 := bstep (se 2 (by rfl) ⟨554487, by rfl⟩ : syracuseStep 1478633 = 1108975) B1108975
theorem B1478783 : Blo 984595 1478783 := bstep (se 1 (by rfl) ⟨1109087, by rfl⟩ : syracuseStep 1478783 = 2218175) B2218175
theorem B987295 : Blo 984595 987295 := bstep (se 1 (by rfl) ⟨740471, by rfl⟩ : syracuseStep 987295 = 1480943) B1480943
theorem B32936219 : Blo 984595 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B987439 : Blo 984595 987439 := bstep (se 1 (by rfl) ⟨740579, by rfl⟩ : syracuseStep 987439 = 1481159) B1481159
theorem B1249607 : Blo 984595 1249607 := bstep (se 1 (by rfl) ⟨937205, by rfl⟩ : syracuseStep 1249607 = 1874411) B1874411
theorem B1479209 : Blo 984595 1479209 := bstep (se 2 (by rfl) ⟨554703, by rfl⟩ : syracuseStep 1479209 = 1109407) B1109407
theorem B5608061 : Blo 984595 5608061 := bstep (se 3 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 5608061 = 2103023) B2103023
theorem B12620447 : Blo 984595 12620447 := bstep (se 1 (by rfl) ⟨9465335, by rfl⟩ : syracuseStep 12620447 = 18930671) B18930671
theorem B1479401 : Blo 984595 1479401 := bstep (se 2 (by rfl) ⟨554775, by rfl⟩ : syracuseStep 1479401 = 1109551) B1109551
theorem B1479647 : Blo 984595 1479647 := bstep (se 1 (by rfl) ⟨1109735, by rfl⟩ : syracuseStep 1479647 = 2219471) B2219471
theorem B1479707 : Blo 984595 1479707 := bstep (se 1 (by rfl) ⟨1109780, by rfl⟩ : syracuseStep 1479707 = 2219561) B2219561
theorem B56923235 : Blo 984595 56923235 := bstep (se 1 (by rfl) ⟨42692426, by rfl⟩ : syracuseStep 56923235 = 85384853) B85384853
theorem B1250407 : Blo 984595 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B988519 : Blo 984595 988519 := bstep (se 1 (by rfl) ⟨741389, by rfl⟩ : syracuseStep 988519 = 1482779) B1482779
theorem B1480187 : Blo 984595 1480187 := bstep (se 1 (by rfl) ⟨1110140, by rfl⟩ : syracuseStep 1480187 = 2220281) B2220281
theorem B12621419 : Blo 984595 12621419 := bstep (se 1 (by rfl) ⟨9466064, by rfl⟩ : syracuseStep 12621419 = 18932129) B18932129
theorem B1480487 : Blo 984595 1480487 := bstep (se 1 (by rfl) ⟨1110365, by rfl⟩ : syracuseStep 1480487 = 2220731) B2220731
theorem B92215205 : Blo 984595 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B7477595 : Blo 984595 7477595 := bstep (se 1 (by rfl) ⟨5608196, by rfl⟩ : syracuseStep 7477595 = 11216393) B11216393
theorem B8001949 : Blo 984595 8001949 := bstep (se 3 (by rfl) ⟨1500365, by rfl⟩ : syracuseStep 8001949 = 3000731) B3000731
theorem B16030163 : Blo 984595 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B1481447 : Blo 984595 1481447 := bstep (se 1 (by rfl) ⟨1111085, by rfl⟩ : syracuseStep 1481447 = 2222171) B2222171
theorem B1481711 : Blo 984595 1481711 := bstep (se 1 (by rfl) ⟨1111283, by rfl⟩ : syracuseStep 1481711 = 2222567) B2222567
theorem B6331547 : Blo 984595 6331547 := bstep (se 1 (by rfl) ⟨4748660, by rfl⟩ : syracuseStep 6331547 = 9497321) B9497321
theorem B1482011 : Blo 984595 1482011 := bstep (se 1 (by rfl) ⟨1111508, by rfl⟩ : syracuseStep 1482011 = 2223017) B2223017
theorem B1482479 : Blo 984595 1482479 := bstep (se 1 (by rfl) ⟨1111859, by rfl⟩ : syracuseStep 1482479 = 2223719) B2223719
theorem B16883639 : Blo 984595 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B1482731 : Blo 984595 1482731 := bstep (se 1 (by rfl) ⟨1112048, by rfl⟩ : syracuseStep 1482731 = 2224097) B2224097
theorem B81010853 : Blo 984595 81010853 := bstep (se 4 (by rfl) ⟨7594767, by rfl⟩ : syracuseStep 81010853 = 15189535) B15189535
theorem B2499923 : Blo 984595 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B6334031 : Blo 984595 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B3156175 : Blo 984595 3156175 := bstep (se 1 (by rfl) ⟨2367131, by rfl⟩ : syracuseStep 3156175 = 4734263) B4734263
theorem B4991219 : Blo 984595 4991219 := bstep (se 1 (by rfl) ⟨3743414, by rfl⟩ : syracuseStep 4991219 = 7486829) B7486829
theorem B12659449 : Blo 984595 12659449 := bstep (se 2 (by rfl) ⟨4747293, by rfl⟩ : syracuseStep 12659449 = 9494587) B9494587
theorem B5483351 : Blo 984595 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B5615851 : Blo 984595 5615851 := bstep (se 1 (by rfl) ⟨4211888, by rfl⟩ : syracuseStep 5615851 = 8423777) B8423777
theorem B11219309 : Blo 984595 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B3748457 : Blo 984595 3748457 := bstep (se 2 (by rfl) ⟨1405671, by rfl⟩ : syracuseStep 3748457 = 2811343) B2811343
theorem B16233371 : Blo 984595 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B3159071 : Blo 984595 3159071 := bstep (se 1 (by rfl) ⟨2369303, by rfl⟩ : syracuseStep 3159071 = 4738607) B4738607
theorem B829699807 : Blo 984595 829699807 := bstep (se 1 (by rfl) ⟨622274855, by rfl⟩ : syracuseStep 829699807 = 1244549711) B1244549711
theorem B3323807 : Blo 984595 3323807 := bstep (se 1 (by rfl) ⟨2492855, by rfl⟩ : syracuseStep 3323807 = 4985711) B4985711
theorem B4995431 : Blo 984595 4995431 := bstep (se 1 (by rfl) ⟨3746573, by rfl⟩ : syracuseStep 4995431 = 7493147) B7493147
theorem B7485857 : Blo 984595 7485857 := bstep (se 2 (by rfl) ⟨2807196, by rfl⟩ : syracuseStep 7485857 = 5614393) B5614393
theorem B3325103 : Blo 984595 3325103 := bstep (se 1 (by rfl) ⟨2493827, by rfl⟩ : syracuseStep 3325103 = 4987655) B4987655
theorem B3326075 : Blo 984595 3326075 := bstep (se 1 (by rfl) ⟨2494556, by rfl⟩ : syracuseStep 3326075 = 4989113) B4989113
theorem B5129345 : Blo 984595 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B45499715 : Blo 984595 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B103761319 : Blo 984595 103761319 := bstep (se 1 (by rfl) ⟨77820989, by rfl⟩ : syracuseStep 103761319 = 155641979) B155641979
theorem B8538155 : Blo 984595 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B3000889 : Blo 984595 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B3328667 : Blo 984595 3328667 := bstep (se 1 (by rfl) ⟨2496500, by rfl⟩ : syracuseStep 3328667 = 4993001) B4993001
theorem B5000129 : Blo 984595 5000129 := bstep (se 2 (by rfl) ⟨1875048, by rfl⟩ : syracuseStep 5000129 = 3750097) B3750097
theorem B3330719 : Blo 984595 3330719 := bstep (se 1 (by rfl) ⟨2498039, by rfl⟩ : syracuseStep 3330719 = 4996079) B4996079
theorem B2218409 : Blo 984595 2218409 := bstep (se 2 (by rfl) ⟨831903, by rfl⟩ : syracuseStep 2218409 = 1663807) B1663807
theorem B1497647 : Blo 984595 1497647 := bstep (se 1 (by rfl) ⟨1123235, by rfl⟩ : syracuseStep 1497647 = 2246471) B2246471
theorem B2251471 : Blo 984595 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B4217939 : Blo 984595 4217939 := bstep (se 1 (by rfl) ⟨3163454, by rfl⟩ : syracuseStep 4217939 = 6326909) B6326909
theorem B1662059 : Blo 984595 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B3333311 : Blo 984595 3333311 := bstep (se 1 (by rfl) ⟨2499983, by rfl⟩ : syracuseStep 3333311 = 4999967) B4999967
theorem B1662187 : Blo 984595 1662187 := bstep (se 1 (by rfl) ⟨1246640, by rfl⟩ : syracuseStep 1662187 = 2493281) B2493281
theorem B1662619 : Blo 984595 1662619 := bstep (se 1 (by rfl) ⟨1246964, by rfl⟩ : syracuseStep 1662619 = 2493929) B2493929
theorem B2055871 : Blo 984595 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B3335201 : Blo 984595 3335201 := bstep (se 2 (by rfl) ⟨1250700, by rfl⟩ : syracuseStep 3335201 = 2501401) B2501401
theorem B1664617 : Blo 984595 1664617 := bstep (se 2 (by rfl) ⟨624231, by rfl⟩ : syracuseStep 1664617 = 1248463) B1248463
theorem B2222135 : Blo 984595 2222135 := bstep (se 1 (by rfl) ⟨1666601, by rfl⟩ : syracuseStep 2222135 = 3333203) B3333203
theorem B2222459 : Blo 984595 2222459 := bstep (se 1 (by rfl) ⟨1666844, by rfl⟩ : syracuseStep 2222459 = 3333689) B3333689
theorem B1665407 : Blo 984595 1665407 := bstep (se 1 (by rfl) ⟨1249055, by rfl⟩ : syracuseStep 1665407 = 2498111) B2498111
theorem B1403291 : Blo 984595 1403291 := bstep (se 1 (by rfl) ⟨1052468, by rfl⟩ : syracuseStep 1403291 = 2104937) B2104937
theorem B11233889 : Blo 984595 11233889 := bstep (se 2 (by rfl) ⟨4212708, by rfl⟩ : syracuseStep 11233889 = 8425417) B8425417
theorem B2222729 : Blo 984595 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B6318911 : Blo 984595 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B1109083 : Blo 984595 1109083 := bstep (se 1 (by rfl) ⟨831812, by rfl⟩ : syracuseStep 1109083 = 1663625) B1663625
theorem B2223881 : Blo 984595 2223881 := bstep (se 2 (by rfl) ⟨833955, by rfl⟩ : syracuseStep 2223881 = 1667911) B1667911
theorem B25259849 : Blo 984595 25259849 := bstep (se 2 (by rfl) ⟨9472443, by rfl⟩ : syracuseStep 25259849 = 18944887) B18944887
theorem B7106383 : Blo 984595 7106383 := bstep (se 1 (by rfl) ⟨5329787, by rfl⟩ : syracuseStep 7106383 = 10659575) B10659575
theorem B1667695 : Blo 984595 1667695 := bstep (se 1 (by rfl) ⟨1250771, by rfl⟩ : syracuseStep 1667695 = 2501543) B2501543
theorem B7500923 : Blo 984595 7500923 := bstep (se 1 (by rfl) ⟨5625692, by rfl⟩ : syracuseStep 7500923 = 11251385) B11251385
theorem B1111423 : Blo 984595 1111423 := bstep (se 1 (by rfl) ⟨833567, by rfl⟩ : syracuseStep 1111423 = 1667135) B1667135
theorem B5993999 : Blo 984595 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B4749139 : Blo 984595 4749139 := bstep (se 1 (by rfl) ⟨3561854, by rfl⟩ : syracuseStep 4749139 = 7123709) B7123709
theorem B25952993 : Blo 984595 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B138348425 : Blo 984595 138348425 := bstep (se 2 (by rfl) ⟨51880659, by rfl⟩ : syracuseStep 138348425 = 103761319) B103761319
theorem B985247 : Blo 984595 985247 := bstep (se 1 (by rfl) ⟨738935, by rfl⟩ : syracuseStep 985247 = 1477871) B1477871
theorem B985583 : Blo 984595 985583 := bstep (se 1 (by rfl) ⟨739187, by rfl⟩ : syracuseStep 985583 = 1478375) B1478375
theorem B985691 : Blo 984595 985691 := bstep (se 1 (by rfl) ⟨739268, by rfl⟩ : syracuseStep 985691 = 1478537) B1478537
theorem B985755 : Blo 984595 985755 := bstep (se 1 (by rfl) ⟨739316, by rfl⟩ : syracuseStep 985755 = 1478633) B1478633
theorem B985855 : Blo 984595 985855 := bstep (se 1 (by rfl) ⟨739391, by rfl⟩ : syracuseStep 985855 = 1478783) B1478783
theorem B21957479 : Blo 984595 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B986139 : Blo 984595 986139 := bstep (se 1 (by rfl) ⟨739604, by rfl⟩ : syracuseStep 986139 = 1479209) B1479209
theorem B3738707 : Blo 984595 3738707 := bstep (se 1 (by rfl) ⟨2804030, by rfl⟩ : syracuseStep 3738707 = 5608061) B5608061
theorem B986267 : Blo 984595 986267 := bstep (se 1 (by rfl) ⟨739700, by rfl⟩ : syracuseStep 986267 = 1479401) B1479401
theorem B986431 : Blo 984595 986431 := bstep (se 1 (by rfl) ⟨739823, by rfl⟩ : syracuseStep 986431 = 1479647) B1479647
theorem B986471 : Blo 984595 986471 := bstep (se 1 (by rfl) ⟨739853, by rfl⟩ : syracuseStep 986471 = 1479707) B1479707
theorem B37948823 : Blo 984595 37948823 := bstep (se 1 (by rfl) ⟨28461617, by rfl⟩ : syracuseStep 37948823 = 56923235) B56923235
theorem B4001185 : Blo 984595 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B16879265 : Blo 984595 16879265 := bstep (se 2 (by rfl) ⟨6329724, by rfl⟩ : syracuseStep 16879265 = 12659449) B12659449
theorem B986791 : Blo 984595 986791 := bstep (se 1 (by rfl) ⟨740093, by rfl⟩ : syracuseStep 986791 = 1480187) B1480187
theorem B986991 : Blo 984595 986991 := bstep (se 1 (by rfl) ⟨740243, by rfl⟩ : syracuseStep 986991 = 1480487) B1480487
theorem B108138401 : Blo 984595 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B61476803 : Blo 984595 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B1478777 : Blo 984595 1478777 := bstep (se 2 (by rfl) ⟨554541, by rfl⟩ : syracuseStep 1478777 = 1109083) B1109083
theorem B4985063 : Blo 984595 4985063 := bstep (se 1 (by rfl) ⟨3738797, by rfl⟩ : syracuseStep 4985063 = 7477595) B7477595
theorem B1478939 : Blo 984595 1478939 := bstep (se 1 (by rfl) ⟨1109204, by rfl⟩ : syracuseStep 1478939 = 2218409) B2218409
theorem B987631 : Blo 984595 987631 := bstep (se 1 (by rfl) ⟨740723, by rfl⟩ : syracuseStep 987631 = 1481447) B1481447
theorem B987807 : Blo 984595 987807 := bstep (se 1 (by rfl) ⟨740855, by rfl⟩ : syracuseStep 987807 = 1481711) B1481711
theorem B988007 : Blo 984595 988007 := bstep (se 1 (by rfl) ⟨741005, by rfl⟩ : syracuseStep 988007 = 1482011) B1482011
theorem B9475177 : Blo 984595 9475177 := bstep (se 2 (by rfl) ⟨3553191, by rfl⟩ : syracuseStep 9475177 = 7106383) B7106383
theorem B988319 : Blo 984595 988319 := bstep (se 1 (by rfl) ⟨741239, by rfl⟩ : syracuseStep 988319 = 1482479) B1482479
theorem B988487 : Blo 984595 988487 := bstep (se 1 (by rfl) ⟨741365, by rfl⟩ : syracuseStep 988487 = 1482731) B1482731
theorem B54007235 : Blo 984595 54007235 := bstep (se 1 (by rfl) ⟨40505426, by rfl⟩ : syracuseStep 54007235 = 81010853) B81010853
theorem B3742109 : Blo 984595 3742109 := bstep (se 3 (by rfl) ⟨701645, by rfl⟩ : syracuseStep 3742109 = 1403291) B1403291
theorem B1481423 : Blo 984595 1481423 := bstep (se 1 (by rfl) ⟨1111067, by rfl⟩ : syracuseStep 1481423 = 2222135) B2222135
theorem B1481639 : Blo 984595 1481639 := bstep (se 1 (by rfl) ⟨1111229, by rfl⟩ : syracuseStep 1481639 = 2222459) B2222459
theorem B1481819 : Blo 984595 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B1481897 : Blo 984595 1481897 := bstep (se 2 (by rfl) ⟨555711, by rfl⟩ : syracuseStep 1481897 = 1111423) B1111423
theorem B6332185 : Blo 984595 6332185 := bstep (se 2 (by rfl) ⟨2374569, by rfl⟩ : syracuseStep 6332185 = 4749139) B4749139
theorem B1482587 : Blo 984595 1482587 := bstep (se 1 (by rfl) ⟨1111940, by rfl⟩ : syracuseStep 1482587 = 2223881) B2223881
theorem B7479539 : Blo 984595 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B2498971 : Blo 984595 2498971 := bstep (se 1 (by rfl) ⟨1874228, by rfl⟩ : syracuseStep 2498971 = 3748457) B3748457
theorem B10822247 : Blo 984595 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B2106047 : Blo 984595 2106047 := bstep (se 1 (by rfl) ⟨1579535, by rfl⟩ : syracuseStep 2106047 = 3159071) B3159071
theorem B4990571 : Blo 984595 4990571 := bstep (se 1 (by rfl) ⟨3742928, by rfl⟩ : syracuseStep 4990571 = 7485857) B7485857
theorem B3419563 : Blo 984595 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B2994515 : Blo 984595 2994515 := bstep (se 1 (by rfl) ⟨2245886, by rfl⟩ : syracuseStep 2994515 = 4491773) B4491773
theorem B4208233 : Blo 984595 4208233 := bstep (se 2 (by rfl) ⟨1578087, by rfl⟩ : syracuseStep 4208233 = 3156175) B3156175
theorem B11255759 : Blo 984595 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B7487801 : Blo 984595 7487801 := bstep (se 2 (by rfl) ⟨2807925, by rfl⟩ : syracuseStep 7487801 = 5615851) B5615851
theorem B42747101 : Blo 984595 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B3327479 : Blo 984595 3327479 := bstep (se 1 (by rfl) ⟨2495609, by rfl⟩ : syracuseStep 3327479 = 4991219) B4991219
theorem B7489259 : Blo 984595 7489259 := bstep (se 1 (by rfl) ⟨5616944, by rfl⟩ : syracuseStep 7489259 = 11233889) B11233889
theorem B4212607 : Blo 984595 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B3655567 : Blo 984595 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B1106266409 : Blo 984595 1106266409 := bstep (se 2 (by rfl) ⟨414849903, by rfl⟩ : syracuseStep 1106266409 = 829699807) B829699807
theorem B10669265 : Blo 984595 10669265 := bstep (se 2 (by rfl) ⟨4000974, by rfl⟩ : syracuseStep 10669265 = 8001949) B8001949
theorem B5000615 : Blo 984595 5000615 := bstep (se 1 (by rfl) ⟨3750461, by rfl⟩ : syracuseStep 5000615 = 7500923) B7500923
theorem B3001961 : Blo 984595 3001961 := bstep (se 2 (by rfl) ⟨1125735, by rfl⟩ : syracuseStep 3001961 = 2251471) B2251471
theorem B10964645 : Blo 984595 10964645 := bstep (se 4 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 10964645 = 2055871) B2055871
theorem B2215871 : Blo 984595 2215871 := bstep (se 1 (by rfl) ⟨1661903, by rfl⟩ : syracuseStep 2215871 = 3323807) B3323807
theorem B3330287 : Blo 984595 3330287 := bstep (se 1 (by rfl) ⟨2497715, by rfl⟩ : syracuseStep 3330287 = 4995431) B4995431
theorem B2216249 : Blo 984595 2216249 := bstep (se 2 (by rfl) ⟨831093, by rfl⟩ : syracuseStep 2216249 = 1662187) B1662187
theorem B2216735 : Blo 984595 2216735 := bstep (se 1 (by rfl) ⟨1662551, by rfl⟩ : syracuseStep 2216735 = 3325103) B3325103
theorem B2216825 : Blo 984595 2216825 := bstep (se 2 (by rfl) ⟨831309, by rfl⟩ : syracuseStep 2216825 = 1662619) B1662619
theorem B2217383 : Blo 984595 2217383 := bstep (se 1 (by rfl) ⟨1663037, by rfl⟩ : syracuseStep 2217383 = 3326075) B3326075
theorem B3332285 : Blo 984595 3332285 := bstep (se 3 (by rfl) ⟨624803, by rfl⟩ : syracuseStep 3332285 = 1249607) B1249607
theorem B30333143 : Blo 984595 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B5692103 : Blo 984595 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B2219111 : Blo 984595 2219111 := bstep (se 1 (by rfl) ⟨1664333, by rfl⟩ : syracuseStep 2219111 = 3328667) B3328667
theorem B3333419 : Blo 984595 3333419 := bstep (se 1 (by rfl) ⟨2500064, by rfl⟩ : syracuseStep 3333419 = 5000129) B5000129
theorem B2219489 : Blo 984595 2219489 := bstep (se 2 (by rfl) ⟨832308, by rfl⟩ : syracuseStep 2219489 = 1664617) B1664617
theorem B4743143 : Blo 984595 4743143 := bstep (se 1 (by rfl) ⟨3557357, by rfl⟩ : syracuseStep 4743143 = 7114715) B7114715
theorem B8413631 : Blo 984595 8413631 := bstep (se 1 (by rfl) ⟨6310223, by rfl⟩ : syracuseStep 8413631 = 12620447) B12620447
theorem B2220479 : Blo 984595 2220479 := bstep (se 1 (by rfl) ⟨1665359, by rfl⟩ : syracuseStep 2220479 = 3330719) B3330719
theorem B8414279 : Blo 984595 8414279 := bstep (se 1 (by rfl) ⟨6310709, by rfl⟩ : syracuseStep 8414279 = 12621419) B12621419
theorem B1664489 : Blo 984595 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B2811959 : Blo 984595 2811959 := bstep (se 1 (by rfl) ⟨2108969, by rfl⟩ : syracuseStep 2811959 = 4217939) B4217939
theorem B1108039 : Blo 984595 1108039 := bstep (se 1 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 1108039 = 1662059) B1662059
theorem B4221031 : Blo 984595 4221031 := bstep (se 1 (by rfl) ⟨3165773, by rfl⟩ : syracuseStep 4221031 = 6331547) B6331547
theorem B2222207 : Blo 984595 2222207 := bstep (se 1 (by rfl) ⟨1666655, by rfl⟩ : syracuseStep 2222207 = 3333311) B3333311
theorem B2223467 : Blo 984595 2223467 := bstep (se 1 (by rfl) ⟨1667600, by rfl⟩ : syracuseStep 2223467 = 3335201) B3335201
theorem B2223593 : Blo 984595 2223593 := bstep (se 2 (by rfl) ⟨833847, by rfl⟩ : syracuseStep 2223593 = 1667695) B1667695
theorem B1666615 : Blo 984595 1666615 := bstep (se 1 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 1666615 = 2499923) B2499923
theorem B4222687 : Blo 984595 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B3993725 : Blo 984595 3993725 := bstep (se 3 (by rfl) ⟨748823, by rfl⟩ : syracuseStep 3993725 = 1497647) B1497647
theorem B1667209 : Blo 984595 1667209 := bstep (se 2 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 1667209 = 1250407) B1250407
theorem B1110271 : Blo 984595 1110271 := bstep (se 1 (by rfl) ⟨832703, by rfl⟩ : syracuseStep 1110271 = 1665407) B1665407
theorem B16839899 : Blo 984595 16839899 := bstep (se 1 (by rfl) ⟨12629924, by rfl⟩ : syracuseStep 16839899 = 25259849) B25259849
theorem B3995999 : Blo 984595 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B17301995 : Blo 984595 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B737510939 : Blo 984595 737510939 := bstep (se 1 (by rfl) ⟨553133204, by rfl⟩ : syracuseStep 737510939 = 1106266409) B1106266409
theorem B2492471 : Blo 984595 2492471 := bstep (se 1 (by rfl) ⟨1869353, by rfl⟩ : syracuseStep 2492471 = 3738707) B3738707
theorem B7112843 : Blo 984595 7112843 := bstep (se 1 (by rfl) ⟨5334632, by rfl⟩ : syracuseStep 7112843 = 10669265) B10669265
theorem B25299215 : Blo 984595 25299215 := bstep (se 1 (by rfl) ⟨18974411, by rfl⟩ : syracuseStep 25299215 = 37948823) B37948823
theorem B2001307 : Blo 984595 2001307 := bstep (se 1 (by rfl) ⟨1500980, by rfl⟩ : syracuseStep 2001307 = 3001961) B3001961
theorem B7309763 : Blo 984595 7309763 := bstep (se 1 (by rfl) ⟨5482322, by rfl⟩ : syracuseStep 7309763 = 10964645) B10964645
theorem B72092267 : Blo 984595 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B1477247 : Blo 984595 1477247 := bstep (se 1 (by rfl) ⟨1107935, by rfl⟩ : syracuseStep 1477247 = 2215871) B2215871
theorem B985851 : Blo 984595 985851 := bstep (se 1 (by rfl) ⟨739388, by rfl⟩ : syracuseStep 985851 = 1478777) B1478777
theorem B1477385 : Blo 984595 1477385 := bstep (se 2 (by rfl) ⟨554019, by rfl⟩ : syracuseStep 1477385 = 1108039) B1108039
theorem B985959 : Blo 984595 985959 := bstep (se 1 (by rfl) ⟨739469, by rfl⟩ : syracuseStep 985959 = 1478939) B1478939
theorem B1477499 : Blo 984595 1477499 := bstep (se 1 (by rfl) ⟨1108124, by rfl⟩ : syracuseStep 1477499 = 2216249) B2216249
theorem B1477823 : Blo 984595 1477823 := bstep (se 1 (by rfl) ⟨1108367, by rfl⟩ : syracuseStep 1477823 = 2216735) B2216735
theorem B1477883 : Blo 984595 1477883 := bstep (se 1 (by rfl) ⟨1108412, by rfl⟩ : syracuseStep 1477883 = 2216825) B2216825
theorem B1478255 : Blo 984595 1478255 := bstep (se 1 (by rfl) ⟨1108691, by rfl⟩ : syracuseStep 1478255 = 2217383) B2217383
theorem B20222095 : Blo 984595 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B2494739 : Blo 984595 2494739 := bstep (se 1 (by rfl) ⟨1871054, by rfl⟩ : syracuseStep 2494739 = 3742109) B3742109
theorem B987615 : Blo 984595 987615 := bstep (se 1 (by rfl) ⟨740711, by rfl⟩ : syracuseStep 987615 = 1481423) B1481423
theorem B4559417 : Blo 984595 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B987759 : Blo 984595 987759 := bstep (se 1 (by rfl) ⟨740819, by rfl⟩ : syracuseStep 987759 = 1481639) B1481639
theorem B987879 : Blo 984595 987879 := bstep (se 1 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 987879 = 1481819) B1481819
theorem B1479407 : Blo 984595 1479407 := bstep (se 1 (by rfl) ⟨1109555, by rfl⟩ : syracuseStep 1479407 = 2219111) B2219111
theorem B987931 : Blo 984595 987931 := bstep (se 1 (by rfl) ⟨740948, by rfl⟩ : syracuseStep 987931 = 1481897) B1481897
theorem B1479659 : Blo 984595 1479659 := bstep (se 1 (by rfl) ⟨1109744, by rfl⟩ : syracuseStep 1479659 = 2219489) B2219489
theorem B988391 : Blo 984595 988391 := bstep (se 1 (by rfl) ⟨741293, by rfl⟩ : syracuseStep 988391 = 1482587) B1482587
theorem B4986359 : Blo 984595 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B5609087 : Blo 984595 5609087 := bstep (se 1 (by rfl) ⟨4206815, by rfl⟩ : syracuseStep 5609087 = 8413631) B8413631
theorem B1480319 : Blo 984595 1480319 := bstep (se 1 (by rfl) ⟨1110239, by rfl⟩ : syracuseStep 1480319 = 2220479) B2220479
theorem B1480361 : Blo 984595 1480361 := bstep (se 2 (by rfl) ⟨555135, by rfl⟩ : syracuseStep 1480361 = 1110271) B1110271
theorem B7214831 : Blo 984595 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B5609519 : Blo 984595 5609519 := bstep (se 1 (by rfl) ⟨4207139, by rfl⟩ : syracuseStep 5609519 = 8414279) B8414279
theorem B1874639 : Blo 984595 1874639 := bstep (se 1 (by rfl) ⟨1405979, by rfl⟩ : syracuseStep 1874639 = 2811959) B2811959
theorem B1481471 : Blo 984595 1481471 := bstep (se 1 (by rfl) ⟨1111103, by rfl⟩ : syracuseStep 1481471 = 2222207) B2222207
theorem B5610977 : Blo 984595 5610977 := bstep (se 2 (by rfl) ⟨2104116, by rfl⟩ : syracuseStep 5610977 = 4208233) B4208233
theorem B1482311 : Blo 984595 1482311 := bstep (se 1 (by rfl) ⟨1111733, by rfl⟩ : syracuseStep 1482311 = 2223467) B2223467
theorem B1482395 : Blo 984595 1482395 := bstep (se 1 (by rfl) ⟨1111796, by rfl⟩ : syracuseStep 1482395 = 2223593) B2223593
theorem B2662483 : Blo 984595 2662483 := bstep (se 1 (by rfl) ⟨1996862, by rfl⟩ : syracuseStep 2662483 = 3993725) B3993725
theorem B2663999 : Blo 984595 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B4991867 : Blo 984595 4991867 := bstep (se 1 (by rfl) ⟨3743900, by rfl⟩ : syracuseStep 4991867 = 7487801) B7487801
theorem B4992839 : Blo 984595 4992839 := bstep (se 1 (by rfl) ⟨3744629, by rfl⟩ : syracuseStep 4992839 = 7489259) B7489259
theorem B5616125 : Blo 984595 5616125 := bstep (se 3 (by rfl) ⟨1053023, by rfl⟩ : syracuseStep 5616125 = 2106047) B2106047
theorem B11252843 : Blo 984595 11252843 := bstep (se 1 (by rfl) ⟨8439632, by rfl⟩ : syracuseStep 11252843 = 16879265) B16879265
theorem B5616809 : Blo 984595 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B3323375 : Blo 984595 3323375 := bstep (se 1 (by rfl) ⟨2492531, by rfl⟩ : syracuseStep 3323375 = 4985063) B4985063
theorem B3162095 : Blo 984595 3162095 := bstep (se 1 (by rfl) ⟨2371571, by rfl⟩ : syracuseStep 3162095 = 4743143) B4743143
theorem B3327047 : Blo 984595 3327047 := bstep (se 1 (by rfl) ⟨2495285, by rfl⟩ : syracuseStep 3327047 = 4990571) B4990571
theorem B12633569 : Blo 984595 12633569 := bstep (se 2 (by rfl) ⟨4737588, by rfl⟩ : syracuseStep 12633569 = 9475177) B9475177
theorem B11226599 : Blo 984595 11226599 := bstep (se 1 (by rfl) ⟨8419949, by rfl⟩ : syracuseStep 11226599 = 16839899) B16839899
theorem B8442913 : Blo 984595 8442913 := bstep (se 2 (by rfl) ⟨3166092, by rfl⟩ : syracuseStep 8442913 = 6332185) B6332185
theorem B3331961 : Blo 984595 3331961 := bstep (se 2 (by rfl) ⟨1249485, by rfl⟩ : syracuseStep 3331961 = 2498971) B2498971
theorem B28498067 : Blo 984595 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B2218319 : Blo 984595 2218319 := bstep (se 1 (by rfl) ⟨1663739, by rfl⟩ : syracuseStep 2218319 = 3327479) B3327479
theorem B92232283 : Blo 984595 92232283 := bstep (se 1 (by rfl) ⟨69174212, by rfl⟩ : syracuseStep 92232283 = 138348425) B138348425
theorem B14638319 : Blo 984595 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B3333743 : Blo 984595 3333743 := bstep (se 1 (by rfl) ⟨2500307, by rfl⟩ : syracuseStep 3333743 = 5000615) B5000615
theorem B4874089 : Blo 984595 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B40984535 : Blo 984595 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B5628041 : Blo 984595 5628041 := bstep (se 2 (by rfl) ⟨2110515, by rfl⟩ : syracuseStep 5628041 = 4221031) B4221031
theorem B2220191 : Blo 984595 2220191 := bstep (se 1 (by rfl) ⟨1665143, by rfl⟩ : syracuseStep 2220191 = 3330287) B3330287
theorem B36004823 : Blo 984595 36004823 := bstep (se 1 (by rfl) ⟨27003617, by rfl⟩ : syracuseStep 36004823 = 54007235) B54007235
theorem B2221523 : Blo 984595 2221523 := bstep (se 1 (by rfl) ⟨1666142, by rfl⟩ : syracuseStep 2221523 = 3332285) B3332285
theorem B3794735 : Blo 984595 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B5334913 : Blo 984595 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B2222153 : Blo 984595 2222153 := bstep (se 2 (by rfl) ⟨833307, by rfl⟩ : syracuseStep 2222153 = 1666615) B1666615
theorem B2222279 : Blo 984595 2222279 := bstep (se 1 (by rfl) ⟨1666709, by rfl⟩ : syracuseStep 2222279 = 3333419) B3333419
theorem B5630249 : Blo 984595 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B2222945 : Blo 984595 2222945 := bstep (se 2 (by rfl) ⟨833604, by rfl⟩ : syracuseStep 2222945 = 1667209) B1667209
theorem B1109659 : Blo 984595 1109659 := bstep (se 1 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 1109659 = 1664489) B1664489
theorem B1996343 : Blo 984595 1996343 := bstep (se 1 (by rfl) ⟨1497257, by rfl⟩ : syracuseStep 1996343 = 2994515) B2994515
theorem B7503839 : Blo 984595 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B11534663 : Blo 984595 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B8422379 : Blo 984595 8422379 := bstep (se 1 (by rfl) ⟨6316784, by rfl⟩ : syracuseStep 8422379 = 12633569) B12633569
theorem B984831 : Blo 984595 984831 := bstep (se 1 (by rfl) ⟨738623, by rfl⟩ : syracuseStep 984831 = 1477247) B1477247
theorem B984923 : Blo 984595 984923 := bstep (se 1 (by rfl) ⟨738692, by rfl⟩ : syracuseStep 984923 = 1477385) B1477385
theorem B984999 : Blo 984595 984999 := bstep (se 1 (by rfl) ⟨738749, by rfl⟩ : syracuseStep 984999 = 1477499) B1477499
theorem B985215 : Blo 984595 985215 := bstep (se 1 (by rfl) ⟨738911, by rfl⟩ : syracuseStep 985215 = 1477823) B1477823
theorem B985255 : Blo 984595 985255 := bstep (se 1 (by rfl) ⟨738941, by rfl⟩ : syracuseStep 985255 = 1477883) B1477883
theorem B985503 : Blo 984595 985503 := bstep (se 1 (by rfl) ⟨739127, by rfl⟩ : syracuseStep 985503 = 1478255) B1478255
theorem B7113217 : Blo 984595 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B986271 : Blo 984595 986271 := bstep (se 1 (by rfl) ⟨739703, by rfl⟩ : syracuseStep 986271 = 1479407) B1479407
theorem B986439 : Blo 984595 986439 := bstep (se 1 (by rfl) ⟨739829, by rfl⟩ : syracuseStep 986439 = 1479659) B1479659
theorem B3739391 : Blo 984595 3739391 := bstep (se 1 (by rfl) ⟨2804543, by rfl⟩ : syracuseStep 3739391 = 5609087) B5609087
theorem B986879 : Blo 984595 986879 := bstep (se 1 (by rfl) ⟨740159, by rfl⟩ : syracuseStep 986879 = 1480319) B1480319
theorem B986907 : Blo 984595 986907 := bstep (se 1 (by rfl) ⟨740180, by rfl⟩ : syracuseStep 986907 = 1480361) B1480361
theorem B3739679 : Blo 984595 3739679 := bstep (se 1 (by rfl) ⟨2804759, by rfl⟩ : syracuseStep 3739679 = 5609519) B5609519
theorem B1478879 : Blo 984595 1478879 := bstep (se 1 (by rfl) ⟨1109159, by rfl⟩ : syracuseStep 1478879 = 2218319) B2218319
theorem B1249759 : Blo 984595 1249759 := bstep (se 1 (by rfl) ⟨937319, by rfl⟩ : syracuseStep 1249759 = 1874639) B1874639
theorem B987647 : Blo 984595 987647 := bstep (se 1 (by rfl) ⟨740735, by rfl⟩ : syracuseStep 987647 = 1481471) B1481471
theorem B1479545 : Blo 984595 1479545 := bstep (se 2 (by rfl) ⟨554829, by rfl⟩ : syracuseStep 1479545 = 1109659) B1109659
theorem B3740651 : Blo 984595 3740651 := bstep (se 1 (by rfl) ⟨2805488, by rfl⟩ : syracuseStep 3740651 = 5610977) B5610977
theorem B988207 : Blo 984595 988207 := bstep (se 1 (by rfl) ⟨741155, by rfl⟩ : syracuseStep 988207 = 1482311) B1482311
theorem B988263 : Blo 984595 988263 := bstep (se 1 (by rfl) ⟨741197, by rfl⟩ : syracuseStep 988263 = 1482395) B1482395
theorem B1480127 : Blo 984595 1480127 := bstep (se 1 (by rfl) ⟨1110095, by rfl⟩ : syracuseStep 1480127 = 2220191) B2220191
theorem B1481015 : Blo 984595 1481015 := bstep (se 1 (by rfl) ⟨1110761, by rfl⟩ : syracuseStep 1481015 = 2221523) B2221523
theorem B1775999 : Blo 984595 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B1481435 : Blo 984595 1481435 := bstep (se 1 (by rfl) ⟨1111076, by rfl⟩ : syracuseStep 1481435 = 2222153) B2222153
theorem B1481519 : Blo 984595 1481519 := bstep (se 1 (by rfl) ⟨1111139, by rfl⟩ : syracuseStep 1481519 = 2222279) B2222279
theorem B1481963 : Blo 984595 1481963 := bstep (se 1 (by rfl) ⟨1111472, by rfl⟩ : syracuseStep 1481963 = 2222945) B2222945
theorem B3744083 : Blo 984595 3744083 := bstep (se 1 (by rfl) ⟨2808062, by rfl⟩ : syracuseStep 3744083 = 5616125) B5616125
theorem B3744539 : Blo 984595 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B6498785 : Blo 984595 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B2108063 : Blo 984595 2108063 := bstep (se 1 (by rfl) ⟨1581047, by rfl⟩ : syracuseStep 2108063 = 3162095) B3162095
theorem B3549977 : Blo 984595 3549977 := bstep (se 2 (by rfl) ⟨1331241, by rfl⟩ : syracuseStep 3549977 = 2662483) B2662483
theorem B7484399 : Blo 984595 7484399 := bstep (se 1 (by rfl) ⟨5613299, by rfl⟩ : syracuseStep 7484399 = 11226599) B11226599
theorem B2668409 : Blo 984595 2668409 := bstep (se 2 (by rfl) ⟨1000653, by rfl⟩ : syracuseStep 2668409 = 2001307) B2001307
theorem B3324239 : Blo 984595 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B3752027 : Blo 984595 3752027 := bstep (se 1 (by rfl) ⟨2814020, by rfl⟩ : syracuseStep 3752027 = 5628041) B5628041
theorem B24003215 : Blo 984595 24003215 := bstep (se 1 (by rfl) ⟨18002411, by rfl⟩ : syracuseStep 24003215 = 36004823) B36004823
theorem B11257217 : Blo 984595 11257217 := bstep (se 2 (by rfl) ⟨4221456, by rfl⟩ : syracuseStep 11257217 = 8442913) B8442913
theorem B3753499 : Blo 984595 3753499 := bstep (se 1 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 3753499 = 5630249) B5630249
theorem B3327911 : Blo 984595 3327911 := bstep (se 1 (by rfl) ⟨2495933, by rfl⟩ : syracuseStep 3327911 = 4991867) B4991867
theorem B3328559 : Blo 984595 3328559 := bstep (se 1 (by rfl) ⟨2496419, by rfl⟩ : syracuseStep 3328559 = 4992839) B4992839
theorem B2215583 : Blo 984595 2215583 := bstep (se 1 (by rfl) ⟨1661687, by rfl⟩ : syracuseStep 2215583 = 3323375) B3323375
theorem B1330895 : Blo 984595 1330895 := bstep (se 1 (by rfl) ⟨998171, by rfl⟩ : syracuseStep 1330895 = 1996343) B1996343
theorem B5002559 : Blo 984595 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B2218031 : Blo 984595 2218031 := bstep (se 1 (by rfl) ⟨1663523, by rfl⟩ : syracuseStep 2218031 = 3327047) B3327047
theorem B491673959 : Blo 984595 491673959 := bstep (se 1 (by rfl) ⟨368755469, by rfl⟩ : syracuseStep 491673959 = 737510939) B737510939
theorem B1661647 : Blo 984595 1661647 := bstep (se 1 (by rfl) ⟨1246235, by rfl⟩ : syracuseStep 1661647 = 2492471) B2492471
theorem B4741895 : Blo 984595 4741895 := bstep (se 1 (by rfl) ⟨3556421, by rfl⟩ : syracuseStep 4741895 = 7112843) B7112843
theorem B16866143 : Blo 984595 16866143 := bstep (se 1 (by rfl) ⟨12649607, by rfl⟩ : syracuseStep 16866143 = 25299215) B25299215
theorem B4873175 : Blo 984595 4873175 := bstep (se 1 (by rfl) ⟨3654881, by rfl⟩ : syracuseStep 4873175 = 7309763) B7309763
theorem B48061511 : Blo 984595 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B1663159 : Blo 984595 1663159 := bstep (se 1 (by rfl) ⟨1247369, by rfl⟩ : syracuseStep 1663159 = 2494739) B2494739
theorem B3039611 : Blo 984595 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B4809887 : Blo 984595 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B2221307 : Blo 984595 2221307 := bstep (se 1 (by rfl) ⟨1665980, by rfl⟩ : syracuseStep 2221307 = 3331961) B3331961
theorem B18998711 : Blo 984595 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B10119293 : Blo 984595 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B9758879 : Blo 984595 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B2222495 : Blo 984595 2222495 := bstep (se 1 (by rfl) ⟨1666871, by rfl⟩ : syracuseStep 2222495 = 3333743) B3333743
theorem B27323023 : Blo 984595 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B26962793 : Blo 984595 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B7501895 : Blo 984595 7501895 := bstep (se 1 (by rfl) ⟨5626421, by rfl⟩ : syracuseStep 7501895 = 11252843) B11252843
theorem B122976377 : Blo 984595 122976377 := bstep (se 2 (by rfl) ⟨46116141, by rfl⟩ : syracuseStep 122976377 = 92232283) B92232283
theorem B7504811 : Blo 984595 7504811 := bstep (se 1 (by rfl) ⟨5628608, by rfl⟩ : syracuseStep 7504811 = 11257217) B11257217
theorem B1477055 : Blo 984595 1477055 := bstep (se 1 (by rfl) ⟨1107791, by rfl⟩ : syracuseStep 1477055 = 2215583) B2215583
theorem B2492927 : Blo 984595 2492927 := bstep (se 1 (by rfl) ⟨1869695, by rfl⟩ : syracuseStep 2492927 = 3739391) B3739391
theorem B2493119 : Blo 984595 2493119 := bstep (se 1 (by rfl) ⟨1869839, by rfl⟩ : syracuseStep 2493119 = 3739679) B3739679
theorem B985919 : Blo 984595 985919 := bstep (se 1 (by rfl) ⟨739439, by rfl⟩ : syracuseStep 985919 = 1478879) B1478879
theorem B986363 : Blo 984595 986363 := bstep (se 1 (by rfl) ⟨739772, by rfl⟩ : syracuseStep 986363 = 1479545) B1479545
theorem B2493767 : Blo 984595 2493767 := bstep (se 1 (by rfl) ⟨1870325, by rfl⟩ : syracuseStep 2493767 = 3740651) B3740651
theorem B986751 : Blo 984595 986751 := bstep (se 1 (by rfl) ⟨740063, by rfl⟩ : syracuseStep 986751 = 1480127) B1480127
theorem B1478687 : Blo 984595 1478687 := bstep (se 1 (by rfl) ⟨1109015, by rfl⟩ : syracuseStep 1478687 = 2218031) B2218031
theorem B987343 : Blo 984595 987343 := bstep (se 1 (by rfl) ⟨740507, by rfl⟩ : syracuseStep 987343 = 1481015) B1481015
theorem B327782639 : Blo 984595 327782639 := bstep (se 1 (by rfl) ⟨245836979, by rfl⟩ : syracuseStep 327782639 = 491673959) B491673959
theorem B1183999 : Blo 984595 1183999 := bstep (se 1 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 1183999 = 1775999) B1775999
theorem B987623 : Blo 984595 987623 := bstep (se 1 (by rfl) ⟨740717, by rfl⟩ : syracuseStep 987623 = 1481435) B1481435
theorem B987679 : Blo 984595 987679 := bstep (se 1 (by rfl) ⟨740759, by rfl⟩ : syracuseStep 987679 = 1481519) B1481519
theorem B11244095 : Blo 984595 11244095 := bstep (se 1 (by rfl) ⟨8433071, by rfl⟩ : syracuseStep 11244095 = 16866143) B16866143
theorem B3248783 : Blo 984595 3248783 := bstep (se 1 (by rfl) ⟨2436587, by rfl⟩ : syracuseStep 3248783 = 4873175) B4873175
theorem B987975 : Blo 984595 987975 := bstep (se 1 (by rfl) ⟨740981, by rfl⟩ : syracuseStep 987975 = 1481963) B1481963
theorem B2496055 : Blo 984595 2496055 := bstep (se 1 (by rfl) ⟨1872041, by rfl⟩ : syracuseStep 2496055 = 3744083) B3744083
theorem B2496359 : Blo 984595 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B1480871 : Blo 984595 1480871 := bstep (se 1 (by rfl) ⟨1110653, by rfl⟩ : syracuseStep 1480871 = 2221307) B2221307
theorem B1481663 : Blo 984595 1481663 := bstep (se 1 (by rfl) ⟨1111247, by rfl⟩ : syracuseStep 1481663 = 2222495) B2222495
theorem B4332523 : Blo 984595 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B2366651 : Blo 984595 2366651 := bstep (se 1 (by rfl) ⟨1774988, by rfl⟩ : syracuseStep 2366651 = 3549977) B3549977
theorem B4989599 : Blo 984595 4989599 := bstep (se 1 (by rfl) ⟨3742199, by rfl⟩ : syracuseStep 4989599 = 7484399) B7484399
theorem B1778939 : Blo 984595 1778939 := bstep (se 1 (by rfl) ⟨1334204, by rfl⟩ : syracuseStep 1778939 = 2668409) B2668409
theorem B3549053 : Blo 984595 3549053 := bstep (se 3 (by rfl) ⟨665447, by rfl⟩ : syracuseStep 3549053 = 1330895) B1330895
theorem B2501351 : Blo 984595 2501351 := bstep (se 1 (by rfl) ⟨1876013, by rfl⟩ : syracuseStep 2501351 = 3752027) B3752027
theorem B16002143 : Blo 984595 16002143 := bstep (se 1 (by rfl) ⟨12001607, by rfl⟩ : syracuseStep 16002143 = 24003215) B24003215
theorem B5614919 : Blo 984595 5614919 := bstep (se 1 (by rfl) ⟨4211189, by rfl⟩ : syracuseStep 5614919 = 8422379) B8422379
theorem B9484289 : Blo 984595 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B32422517 : Blo 984595 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B3161263 : Blo 984595 3161263 := bstep (se 1 (by rfl) ⟨2370947, by rfl⟩ : syracuseStep 3161263 = 4741895) B4741895
theorem B12665807 : Blo 984595 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B6505919 : Blo 984595 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B5621501 : Blo 984595 5621501 := bstep (se 3 (by rfl) ⟨1054031, by rfl⟩ : syracuseStep 5621501 = 2108063) B2108063
theorem B17975195 : Blo 984595 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B2215529 : Blo 984595 2215529 := bstep (se 2 (by rfl) ⟨830823, by rfl⟩ : syracuseStep 2215529 = 1661647) B1661647
theorem B5001263 : Blo 984595 5001263 := bstep (se 1 (by rfl) ⟨3750947, by rfl⟩ : syracuseStep 5001263 = 7501895) B7501895
theorem B2216159 : Blo 984595 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B7689775 : Blo 984595 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B2217545 : Blo 984595 2217545 := bstep (se 2 (by rfl) ⟨831579, by rfl⟩ : syracuseStep 2217545 = 1663159) B1663159
theorem B2218607 : Blo 984595 2218607 := bstep (se 1 (by rfl) ⟨1663955, by rfl⟩ : syracuseStep 2218607 = 3327911) B3327911
theorem B2219039 : Blo 984595 2219039 := bstep (se 1 (by rfl) ⟨1664279, by rfl⟩ : syracuseStep 2219039 = 3328559) B3328559
theorem B5004665 : Blo 984595 5004665 := bstep (se 2 (by rfl) ⟨1876749, by rfl⟩ : syracuseStep 5004665 = 3753499) B3753499
theorem B36430697 : Blo 984595 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B3335039 : Blo 984595 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B32041007 : Blo 984595 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B1666345 : Blo 984595 1666345 := bstep (se 2 (by rfl) ⟨624879, by rfl⟩ : syracuseStep 1666345 = 1249759) B1249759
theorem B3206591 : Blo 984595 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B6746195 : Blo 984595 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B81984251 : Blo 984595 81984251 := bstep (se 1 (by rfl) ⟨61488188, by rfl⟩ : syracuseStep 81984251 = 122976377) B122976377
theorem B984703 : Blo 984595 984703 := bstep (se 1 (by rfl) ⟨738527, by rfl⟩ : syracuseStep 984703 = 1477055) B1477055
theorem B1477019 : Blo 984595 1477019 := bstep (se 1 (by rfl) ⟨1107764, by rfl⟩ : syracuseStep 1477019 = 2215529) B2215529
theorem B985791 : Blo 984595 985791 := bstep (se 1 (by rfl) ⟨739343, by rfl⟩ : syracuseStep 985791 = 1478687) B1478687
theorem B1477439 : Blo 984595 1477439 := bstep (se 1 (by rfl) ⟨1108079, by rfl⟩ : syracuseStep 1477439 = 2216159) B2216159
theorem B2165855 : Blo 984595 2165855 := bstep (se 1 (by rfl) ⟨1624391, by rfl⟩ : syracuseStep 2165855 = 3248783) B3248783
theorem B1478363 : Blo 984595 1478363 := bstep (se 1 (by rfl) ⟨1108772, by rfl⟩ : syracuseStep 1478363 = 2217545) B2217545
theorem B987247 : Blo 984595 987247 := bstep (se 1 (by rfl) ⟨740435, by rfl⟩ : syracuseStep 987247 = 1480871) B1480871
theorem B1479071 : Blo 984595 1479071 := bstep (se 1 (by rfl) ⟨1109303, by rfl⟩ : syracuseStep 1479071 = 2218607) B2218607
theorem B987775 : Blo 984595 987775 := bstep (se 1 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 987775 = 1481663) B1481663
theorem B1479359 : Blo 984595 1479359 := bstep (se 1 (by rfl) ⟨1109519, by rfl⟩ : syracuseStep 1479359 = 2219039) B2219039
theorem B1577767 : Blo 984595 1577767 := bstep (se 1 (by rfl) ⟨1183325, by rfl⟩ : syracuseStep 1577767 = 2366651) B2366651
theorem B1578665 : Blo 984595 1578665 := bstep (se 2 (by rfl) ⟨591999, by rfl⟩ : syracuseStep 1578665 = 1183999) B1183999
theorem B24287131 : Blo 984595 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B1185959 : Blo 984595 1185959 := bstep (se 1 (by rfl) ⟨889469, by rfl⟩ : syracuseStep 1185959 = 1778939) B1778939
theorem B3743279 : Blo 984595 3743279 := bstep (se 1 (by rfl) ⟨2807459, by rfl⟩ : syracuseStep 3743279 = 5614919) B5614919
theorem B2137727 : Blo 984595 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B4497463 : Blo 984595 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B5776697 : Blo 984595 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B4337279 : Blo 984595 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B3747667 : Blo 984595 3747667 := bstep (se 1 (by rfl) ⟨2810750, by rfl⟩ : syracuseStep 3747667 = 5621501) B5621501
theorem B3326399 : Blo 984595 3326399 := bstep (se 1 (by rfl) ⟨2494799, by rfl⟩ : syracuseStep 3326399 = 4989599) B4989599
theorem B10668095 : Blo 984595 10668095 := bstep (se 1 (by rfl) ⟨8001071, by rfl⟩ : syracuseStep 10668095 = 16002143) B16002143
theorem B3328073 : Blo 984595 3328073 := bstep (se 2 (by rfl) ⟨1248027, by rfl⟩ : syracuseStep 3328073 = 2496055) B2496055
theorem B4215017 : Blo 984595 4215017 := bstep (se 2 (by rfl) ⟨1580631, by rfl⟩ : syracuseStep 4215017 = 3161263) B3161263
theorem B21615011 : Blo 984595 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B5003207 : Blo 984595 5003207 := bstep (se 1 (by rfl) ⟨3752405, by rfl⟩ : syracuseStep 5003207 = 7504811) B7504811
theorem B8443871 : Blo 984595 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B11983463 : Blo 984595 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B1661951 : Blo 984595 1661951 := bstep (se 1 (by rfl) ⟨1246463, by rfl⟩ : syracuseStep 1661951 = 2492927) B2492927
theorem B1662079 : Blo 984595 1662079 := bstep (se 1 (by rfl) ⟨1246559, by rfl⟩ : syracuseStep 1662079 = 2493119) B2493119
theorem B1662511 : Blo 984595 1662511 := bstep (se 1 (by rfl) ⟨1246883, by rfl⟩ : syracuseStep 1662511 = 2493767) B2493767
theorem B3334175 : Blo 984595 3334175 := bstep (se 1 (by rfl) ⟨2500631, by rfl⟩ : syracuseStep 3334175 = 5001263) B5001263
theorem B218521759 : Blo 984595 218521759 := bstep (se 1 (by rfl) ⟨163891319, by rfl⟩ : syracuseStep 218521759 = 327782639) B327782639
theorem B7496063 : Blo 984595 7496063 := bstep (se 1 (by rfl) ⟨5622047, by rfl⟩ : syracuseStep 7496063 = 11244095) B11244095
theorem B1664239 : Blo 984595 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B2221793 : Blo 984595 2221793 := bstep (se 2 (by rfl) ⟨833172, by rfl⟩ : syracuseStep 2221793 = 1666345) B1666345
theorem B3336443 : Blo 984595 3336443 := bstep (se 1 (by rfl) ⟨2502332, by rfl⟩ : syracuseStep 3336443 = 5004665) B5004665
theorem B9464141 : Blo 984595 9464141 := bstep (se 3 (by rfl) ⟨1774526, by rfl⟩ : syracuseStep 9464141 = 3549053) B3549053
theorem B2223359 : Blo 984595 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B21360671 : Blo 984595 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B1667567 : Blo 984595 1667567 := bstep (se 1 (by rfl) ⟨1250675, by rfl⟩ : syracuseStep 1667567 = 2501351) B2501351
theorem B10253033 : Blo 984595 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B6322859 : Blo 984595 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B54656167 : Blo 984595 54656167 := bstep (se 1 (by rfl) ⟨40992125, by rfl⟩ : syracuseStep 54656167 = 81984251) B81984251
theorem B23986469 : Blo 984595 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B23102453 : Blo 984595 23102453 := bstep (se 5 (by rfl) ⟨1082927, by rfl⟩ : syracuseStep 23102453 = 2165855) B2165855
theorem B7112063 : Blo 984595 7112063 := bstep (se 1 (by rfl) ⟨5334047, by rfl⟩ : syracuseStep 7112063 = 10668095) B10668095
theorem B984679 : Blo 984595 984679 := bstep (se 1 (by rfl) ⟨738509, by rfl⟩ : syracuseStep 984679 = 1477019) B1477019
theorem B984959 : Blo 984595 984959 := bstep (se 1 (by rfl) ⟨738719, by rfl⟩ : syracuseStep 984959 = 1477439) B1477439
theorem B985575 : Blo 984595 985575 := bstep (se 1 (by rfl) ⟨739181, by rfl⟩ : syracuseStep 985575 = 1478363) B1478363
theorem B986047 : Blo 984595 986047 := bstep (se 1 (by rfl) ⟨739535, by rfl⟩ : syracuseStep 986047 = 1479071) B1479071
theorem B986239 : Blo 984595 986239 := bstep (se 1 (by rfl) ⟨739679, by rfl⟩ : syracuseStep 986239 = 1479359) B1479359
theorem B15404525 : Blo 984595 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B1052443 : Blo 984595 1052443 := bstep (se 1 (by rfl) ⟨789332, by rfl⟩ : syracuseStep 1052443 = 1578665) B1578665
theorem B2495519 : Blo 984595 2495519 := bstep (se 1 (by rfl) ⟨1871639, by rfl⟩ : syracuseStep 2495519 = 3743279) B3743279
theorem B2103689 : Blo 984595 2103689 := bstep (se 2 (by rfl) ⟨788883, by rfl⟩ : syracuseStep 2103689 = 1577767) B1577767
theorem B1481195 : Blo 984595 1481195 := bstep (se 1 (by rfl) ⟨1110896, by rfl⟩ : syracuseStep 1481195 = 2221793) B2221793
theorem B1482239 : Blo 984595 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B2891519 : Blo 984595 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B32382841 : Blo 984595 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B1425151 : Blo 984595 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B4996889 : Blo 984595 4996889 := bstep (se 2 (by rfl) ⟨1873833, by rfl⟩ : syracuseStep 4996889 = 3747667) B3747667
theorem B4997375 : Blo 984595 4997375 := bstep (se 1 (by rfl) ⟨3748031, by rfl⟩ : syracuseStep 4997375 = 7496063) B7496063
theorem B3162557 : Blo 984595 3162557 := bstep (se 3 (by rfl) ⟨592979, by rfl⟩ : syracuseStep 3162557 = 1185959) B1185959
theorem B6309427 : Blo 984595 6309427 := bstep (se 1 (by rfl) ⟨4732070, by rfl⟩ : syracuseStep 6309427 = 9464141) B9464141
theorem B14240447 : Blo 984595 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B6835355 : Blo 984595 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B2216105 : Blo 984595 2216105 := bstep (se 2 (by rfl) ⟨831039, by rfl⟩ : syracuseStep 2216105 = 1662079) B1662079
theorem B4215239 : Blo 984595 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B2216681 : Blo 984595 2216681 := bstep (se 2 (by rfl) ⟨831255, by rfl⟩ : syracuseStep 2216681 = 1662511) B1662511
theorem B291362345 : Blo 984595 291362345 := bstep (se 2 (by rfl) ⟨109260879, by rfl⟩ : syracuseStep 291362345 = 218521759) B218521759
theorem B2217599 : Blo 984595 2217599 := bstep (se 1 (by rfl) ⟨1663199, by rfl⟩ : syracuseStep 2217599 = 3326399) B3326399
theorem B2218715 : Blo 984595 2218715 := bstep (se 1 (by rfl) ⟨1664036, by rfl⟩ : syracuseStep 2218715 = 3328073) B3328073
theorem B2218985 : Blo 984595 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B2810011 : Blo 984595 2810011 := bstep (se 1 (by rfl) ⟨2107508, by rfl⟩ : syracuseStep 2810011 = 4215017) B4215017
theorem B14410007 : Blo 984595 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B3335471 : Blo 984595 3335471 := bstep (se 1 (by rfl) ⟨2501603, by rfl⟩ : syracuseStep 3335471 = 5003207) B5003207
theorem B5629247 : Blo 984595 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B7988975 : Blo 984595 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B1107967 : Blo 984595 1107967 := bstep (se 1 (by rfl) ⟨830975, by rfl⟩ : syracuseStep 1107967 = 1661951) B1661951
theorem B2222783 : Blo 984595 2222783 := bstep (se 1 (by rfl) ⟨1667087, by rfl⟩ : syracuseStep 2222783 = 3334175) B3334175
theorem B2224295 : Blo 984595 2224295 := bstep (se 1 (by rfl) ⟨1668221, by rfl⟩ : syracuseStep 2224295 = 3336443) B3336443
theorem B1111711 : Blo 984595 1111711 := bstep (se 1 (by rfl) ⟨833783, by rfl⟩ : syracuseStep 1111711 = 1667567) B1667567
theorem B72874889 : Blo 984595 72874889 := bstep (se 2 (by rfl) ⟨27328083, by rfl⟩ : syracuseStep 72874889 = 54656167) B54656167
theorem B15990979 : Blo 984595 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B4556903 : Blo 984595 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B61606541 : Blo 984595 61606541 := bstep (se 3 (by rfl) ⟨11551226, by rfl⟩ : syracuseStep 61606541 = 23102453) B23102453
theorem B1477289 : Blo 984595 1477289 := bstep (se 2 (by rfl) ⟨553983, by rfl⟩ : syracuseStep 1477289 = 1107967) B1107967
theorem B1477403 : Blo 984595 1477403 := bstep (se 1 (by rfl) ⟨1108052, by rfl⟩ : syracuseStep 1477403 = 2216105) B2216105
theorem B1477787 : Blo 984595 1477787 := bstep (se 1 (by rfl) ⟨1108340, by rfl⟩ : syracuseStep 1477787 = 2216681) B2216681
theorem B1478399 : Blo 984595 1478399 := bstep (se 1 (by rfl) ⟨1108799, by rfl⟩ : syracuseStep 1478399 = 2217599) B2217599
theorem B987463 : Blo 984595 987463 := bstep (se 1 (by rfl) ⟨740597, by rfl⟩ : syracuseStep 987463 = 1481195) B1481195
theorem B1479143 : Blo 984595 1479143 := bstep (se 1 (by rfl) ⟨1109357, by rfl⟩ : syracuseStep 1479143 = 2218715) B2218715
theorem B1479323 : Blo 984595 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B988159 : Blo 984595 988159 := bstep (se 1 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 988159 = 1482239) B1482239
theorem B9606671 : Blo 984595 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B5609837 : Blo 984595 5609837 := bstep (se 3 (by rfl) ⟨1051844, by rfl⟩ : syracuseStep 5609837 = 2103689) B2103689
theorem B1481855 : Blo 984595 1481855 := bstep (se 1 (by rfl) ⟨1111391, by rfl⟩ : syracuseStep 1481855 = 2222783) B2222783
theorem B1482281 : Blo 984595 1482281 := bstep (se 2 (by rfl) ⟨555855, by rfl⟩ : syracuseStep 1482281 = 1111711) B1111711
theorem B30842869 : Blo 984595 30842869 := bstep (se 5 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 30842869 = 2891519) B2891519
theorem B1482863 : Blo 984595 1482863 := bstep (se 1 (by rfl) ⟨1112147, by rfl⟩ : syracuseStep 1482863 = 2224295) B2224295
theorem B3746681 : Blo 984595 3746681 := bstep (se 2 (by rfl) ⟨1405005, by rfl⟩ : syracuseStep 3746681 = 2810011) B2810011
theorem B2108371 : Blo 984595 2108371 := bstep (se 1 (by rfl) ⟨1581278, by rfl⟩ : syracuseStep 2108371 = 3162557) B3162557
theorem B10269683 : Blo 984595 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B3752831 : Blo 984595 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B5325983 : Blo 984595 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B48583259 : Blo 984595 48583259 := bstep (se 1 (by rfl) ⟨36437444, by rfl⟩ : syracuseStep 48583259 = 72874889) B72874889
theorem B43177121 : Blo 984595 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B3331259 : Blo 984595 3331259 := bstep (se 1 (by rfl) ⟨2498444, by rfl⟩ : syracuseStep 3331259 = 4996889) B4996889
theorem B3331583 : Blo 984595 3331583 := bstep (se 1 (by rfl) ⟨2498687, by rfl⟩ : syracuseStep 3331583 = 4997375) B4997375
theorem B4741375 : Blo 984595 4741375 := bstep (se 1 (by rfl) ⟨3556031, by rfl⟩ : syracuseStep 4741375 = 7112063) B7112063
theorem B9493631 : Blo 984595 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B8412569 : Blo 984595 8412569 := bstep (se 2 (by rfl) ⟨3154713, by rfl⟩ : syracuseStep 8412569 = 6309427) B6309427
theorem B2810159 : Blo 984595 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B1663679 : Blo 984595 1663679 := bstep (se 1 (by rfl) ⟨1247759, by rfl⟩ : syracuseStep 1663679 = 2495519) B2495519
theorem B194241563 : Blo 984595 194241563 := bstep (se 1 (by rfl) ⟨145681172, by rfl⟩ : syracuseStep 194241563 = 291362345) B291362345
theorem B1403257 : Blo 984595 1403257 := bstep (se 2 (by rfl) ⟨526221, by rfl⟩ : syracuseStep 1403257 = 1052443) B1052443
theorem B2223647 : Blo 984595 2223647 := bstep (se 1 (by rfl) ⟨1667735, by rfl⟩ : syracuseStep 2223647 = 3335471) B3335471
theorem B1900201 : Blo 984595 1900201 := bstep (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) B1425151
theorem B984859 : Blo 984595 984859 := bstep (se 1 (by rfl) ⟨738644, by rfl⟩ : syracuseStep 984859 = 1477289) B1477289
theorem B984935 : Blo 984595 984935 := bstep (se 1 (by rfl) ⟨738701, by rfl⟩ : syracuseStep 984935 = 1477403) B1477403
theorem B985191 : Blo 984595 985191 := bstep (se 1 (by rfl) ⟨738893, by rfl⟩ : syracuseStep 985191 = 1477787) B1477787
theorem B985599 : Blo 984595 985599 := bstep (se 1 (by rfl) ⟨739199, by rfl⟩ : syracuseStep 985599 = 1478399) B1478399
theorem B986095 : Blo 984595 986095 := bstep (se 1 (by rfl) ⟨739571, by rfl⟩ : syracuseStep 986095 = 1479143) B1479143
theorem B986215 : Blo 984595 986215 := bstep (se 1 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 986215 = 1479323) B1479323
theorem B1871009 : Blo 984595 1871009 := bstep (se 2 (by rfl) ⟨701628, by rfl⟩ : syracuseStep 1871009 = 1403257) B1403257
theorem B3739891 : Blo 984595 3739891 := bstep (se 1 (by rfl) ⟨2804918, by rfl⟩ : syracuseStep 3739891 = 5609837) B5609837
theorem B6329087 : Blo 984595 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B987903 : Blo 984595 987903 := bstep (se 1 (by rfl) ⟨740927, by rfl⟩ : syracuseStep 987903 = 1481855) B1481855
theorem B5608379 : Blo 984595 5608379 := bstep (se 1 (by rfl) ⟨4206284, by rfl⟩ : syracuseStep 5608379 = 8412569) B8412569
theorem B988187 : Blo 984595 988187 := bstep (se 1 (by rfl) ⟨741140, by rfl⟩ : syracuseStep 988187 = 1482281) B1482281
theorem B988575 : Blo 984595 988575 := bstep (se 1 (by rfl) ⟨741431, by rfl⟩ : syracuseStep 988575 = 1482863) B1482863
theorem B1873439 : Blo 984595 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B2497787 : Blo 984595 2497787 := bstep (se 1 (by rfl) ⟨1873340, by rfl⟩ : syracuseStep 2497787 = 3746681) B3746681
theorem B1482431 : Blo 984595 1482431 := bstep (se 1 (by rfl) ⟨1111823, by rfl⟩ : syracuseStep 1482431 = 2223647) B2223647
theorem B2533601 : Blo 984595 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B2501887 : Blo 984595 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B3550655 : Blo 984595 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B48606965 : Blo 984595 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B32388839 : Blo 984595 32388839 := bstep (se 1 (by rfl) ⟨24291629, by rfl⟩ : syracuseStep 32388839 = 48583259) B48583259
theorem B28784747 : Blo 984595 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B6404447 : Blo 984595 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B164284109 : Blo 984595 164284109 := bstep (se 3 (by rfl) ⟨30803270, by rfl⟩ : syracuseStep 164284109 = 61606541) B61606541
theorem B21321305 : Blo 984595 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B2220839 : Blo 984595 2220839 := bstep (se 1 (by rfl) ⟨1665629, by rfl⟩ : syracuseStep 2220839 = 3331259) B3331259
theorem B2221055 : Blo 984595 2221055 := bstep (se 1 (by rfl) ⟨1665791, by rfl⟩ : syracuseStep 2221055 = 3331583) B3331583
theorem B2811161 : Blo 984595 2811161 := bstep (se 2 (by rfl) ⟨1054185, by rfl⟩ : syracuseStep 2811161 = 2108371) B2108371
theorem B1109119 : Blo 984595 1109119 := bstep (se 1 (by rfl) ⟨831839, by rfl⟩ : syracuseStep 1109119 = 1663679) B1663679
theorem B129494375 : Blo 984595 129494375 := bstep (se 1 (by rfl) ⟨97120781, by rfl⟩ : syracuseStep 129494375 = 194241563) B194241563
theorem B6321833 : Blo 984595 6321833 := bstep (se 2 (by rfl) ⟨2370687, by rfl⟩ : syracuseStep 6321833 = 4741375) B4741375
theorem B6846455 : Blo 984595 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B41123825 : Blo 984595 41123825 := bstep (se 2 (by rfl) ⟨15421434, by rfl⟩ : syracuseStep 41123825 = 30842869) B30842869
theorem B1247339 : Blo 984595 1247339 := bstep (se 1 (by rfl) ⟨935504, by rfl⟩ : syracuseStep 1247339 = 1871009) B1871009
theorem B3738919 : Blo 984595 3738919 := bstep (se 1 (by rfl) ⟨2804189, by rfl⟩ : syracuseStep 3738919 = 5608379) B5608379
theorem B1248959 : Blo 984595 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B1478825 : Blo 984595 1478825 := bstep (se 2 (by rfl) ⟨554559, by rfl⟩ : syracuseStep 1478825 = 1109119) B1109119
theorem B988287 : Blo 984595 988287 := bstep (se 1 (by rfl) ⟨741215, by rfl⟩ : syracuseStep 988287 = 1482431) B1482431
theorem B18257213 : Blo 984595 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B4986521 : Blo 984595 4986521 := bstep (se 2 (by rfl) ⟨1869945, by rfl⟩ : syracuseStep 4986521 = 3739891) B3739891
theorem B1480559 : Blo 984595 1480559 := bstep (se 1 (by rfl) ⟨1110419, by rfl⟩ : syracuseStep 1480559 = 2220839) B2220839
theorem B1480703 : Blo 984595 1480703 := bstep (se 1 (by rfl) ⟨1110527, by rfl⟩ : syracuseStep 1480703 = 2221055) B2221055
theorem B1874107 : Blo 984595 1874107 := bstep (se 1 (by rfl) ⟨1405580, by rfl⟩ : syracuseStep 1874107 = 2811161) B2811161
theorem B17078525 : Blo 984595 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B109522739 : Blo 984595 109522739 := bstep (se 1 (by rfl) ⟨82142054, by rfl⟩ : syracuseStep 109522739 = 164284109) B164284109
theorem B76759325 : Blo 984595 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B1689067 : Blo 984595 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B86329583 : Blo 984595 86329583 := bstep (se 1 (by rfl) ⟨64747187, by rfl⟩ : syracuseStep 86329583 = 129494375) B129494375
theorem B4214555 : Blo 984595 4214555 := bstep (se 1 (by rfl) ⟨3160916, by rfl⟩ : syracuseStep 4214555 = 6321833) B6321833
theorem B27415883 : Blo 984595 27415883 := bstep (se 1 (by rfl) ⟨20561912, by rfl⟩ : syracuseStep 27415883 = 41123825) B41123825
theorem B4219391 : Blo 984595 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B14214203 : Blo 984595 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B3335849 : Blo 984595 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B1665191 : Blo 984595 1665191 := bstep (se 1 (by rfl) ⟨1248893, by rfl⟩ : syracuseStep 1665191 = 2497787) B2497787
theorem B32404643 : Blo 984595 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B21592559 : Blo 984595 21592559 := bstep (se 1 (by rfl) ⟨16194419, by rfl⟩ : syracuseStep 21592559 = 32388839) B32388839
theorem B9468413 : Blo 984595 9468413 := bstep (se 3 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 9468413 = 3550655) B3550655
theorem B985883 : Blo 984595 985883 := bstep (se 1 (by rfl) ⟨739412, by rfl⟩ : syracuseStep 985883 = 1478825) B1478825
theorem B987039 : Blo 984595 987039 := bstep (se 1 (by rfl) ⟨740279, by rfl⟩ : syracuseStep 987039 = 1480559) B1480559
theorem B987135 : Blo 984595 987135 := bstep (se 1 (by rfl) ⟨740351, by rfl⟩ : syracuseStep 987135 = 1480703) B1480703
theorem B4985225 : Blo 984595 4985225 := bstep (se 2 (by rfl) ⟨1869459, by rfl⟩ : syracuseStep 4985225 = 3738919) B3738919
theorem B9476135 : Blo 984595 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B2498809 : Blo 984595 2498809 := bstep (se 2 (by rfl) ⟨937053, by rfl⟩ : syracuseStep 2498809 = 1874107) B1874107
theorem B21603095 : Blo 984595 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B14395039 : Blo 984595 14395039 := bstep (se 1 (by rfl) ⟨10796279, by rfl⟩ : syracuseStep 14395039 = 21592559) B21592559
theorem B57553055 : Blo 984595 57553055 := bstep (se 1 (by rfl) ⟨43164791, by rfl⟩ : syracuseStep 57553055 = 86329583) B86329583
theorem B12171475 : Blo 984595 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B3324347 : Blo 984595 3324347 := bstep (se 1 (by rfl) ⟨2493260, by rfl⟩ : syracuseStep 3324347 = 4986521) B4986521
theorem B11385683 : Blo 984595 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B3326237 : Blo 984595 3326237 := bstep (se 3 (by rfl) ⟨623669, by rfl⟩ : syracuseStep 3326237 = 1247339) B1247339
theorem B6312275 : Blo 984595 6312275 := bstep (se 1 (by rfl) ⟨4734206, by rfl⟩ : syracuseStep 6312275 = 9468413) B9468413
theorem B3330557 : Blo 984595 3330557 := bstep (se 3 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 3330557 = 1248959) B1248959
theorem B51172883 : Blo 984595 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B2252089 : Blo 984595 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B2809703 : Blo 984595 2809703 := bstep (se 1 (by rfl) ⟨2107277, by rfl⟩ : syracuseStep 2809703 = 4214555) B4214555
theorem B18277255 : Blo 984595 18277255 := bstep (se 1 (by rfl) ⟨13707941, by rfl⟩ : syracuseStep 18277255 = 27415883) B27415883
theorem B2812927 : Blo 984595 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B2223899 : Blo 984595 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B1110127 : Blo 984595 1110127 := bstep (se 1 (by rfl) ⟨832595, by rfl⟩ : syracuseStep 1110127 = 1665191) B1665191
theorem B292060637 : Blo 984595 292060637 := bstep (se 3 (by rfl) ⟨54761369, by rfl⟩ : syracuseStep 292060637 = 109522739) B109522739
theorem B64914533 : Blo 984595 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B34115255 : Blo 984595 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B1873135 : Blo 984595 1873135 := bstep (se 1 (by rfl) ⟨1404851, by rfl⟩ : syracuseStep 1873135 = 2809703) B2809703
theorem B1480169 : Blo 984595 1480169 := bstep (se 2 (by rfl) ⟨555063, by rfl⟩ : syracuseStep 1480169 = 1110127) B1110127
theorem B1482599 : Blo 984595 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B4208183 : Blo 984595 4208183 := bstep (se 1 (by rfl) ⟨3156137, by rfl⟩ : syracuseStep 4208183 = 6312275) B6312275
theorem B3323483 : Blo 984595 3323483 := bstep (se 1 (by rfl) ⟨2492612, by rfl⟩ : syracuseStep 3323483 = 4985225) B4985225
theorem B3750569 : Blo 984595 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B14402063 : Blo 984595 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B12011141 : Blo 984595 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B2216231 : Blo 984595 2216231 := bstep (se 1 (by rfl) ⟨1662173, by rfl⟩ : syracuseStep 2216231 = 3324347) B3324347
theorem B7590455 : Blo 984595 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B2217491 : Blo 984595 2217491 := bstep (se 1 (by rfl) ⟨1663118, by rfl⟩ : syracuseStep 2217491 = 3326237) B3326237
theorem B3331745 : Blo 984595 3331745 := bstep (se 2 (by rfl) ⟨1249404, by rfl⟩ : syracuseStep 3331745 = 2498809) B2498809
theorem B24369673 : Blo 984595 24369673 := bstep (se 2 (by rfl) ⟨9138627, by rfl⟩ : syracuseStep 24369673 = 18277255) B18277255
theorem B2220371 : Blo 984595 2220371 := bstep (se 1 (by rfl) ⟨1665278, by rfl⟩ : syracuseStep 2220371 = 3330557) B3330557
theorem B6317423 : Blo 984595 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B38368703 : Blo 984595 38368703 := bstep (se 1 (by rfl) ⟨28776527, by rfl⟩ : syracuseStep 38368703 = 57553055) B57553055
theorem B76773541 : Blo 984595 76773541 := bstep (se 4 (by rfl) ⟨7197519, by rfl⟩ : syracuseStep 76773541 = 14395039) B14395039
theorem B194707091 : Blo 984595 194707091 := bstep (se 1 (by rfl) ⟨146030318, by rfl⟩ : syracuseStep 194707091 = 292060637) B292060637
theorem B9601375 : Blo 984595 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B22743503 : Blo 984595 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B1477487 : Blo 984595 1477487 := bstep (se 1 (by rfl) ⟨1108115, by rfl⟩ : syracuseStep 1477487 = 2216231) B2216231
theorem B986779 : Blo 984595 986779 := bstep (se 1 (by rfl) ⟨740084, by rfl⟩ : syracuseStep 986779 = 1480169) B1480169
theorem B1478327 : Blo 984595 1478327 := bstep (se 1 (by rfl) ⟨1108745, by rfl⟩ : syracuseStep 1478327 = 2217491) B2217491
theorem B988399 : Blo 984595 988399 := bstep (se 1 (by rfl) ⟨741299, by rfl⟩ : syracuseStep 988399 = 1482599) B1482599
theorem B1480247 : Blo 984595 1480247 := bstep (se 1 (by rfl) ⟨1110185, by rfl⟩ : syracuseStep 1480247 = 2220371) B2220371
theorem B2497513 : Blo 984595 2497513 := bstep (se 2 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 2497513 = 1873135) B1873135
theorem B2500379 : Blo 984595 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B129804727 : Blo 984595 129804727 := bstep (se 1 (by rfl) ⟨97353545, by rfl⟩ : syracuseStep 129804727 = 194707091) B194707091
theorem B8007427 : Blo 984595 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B5060303 : Blo 984595 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B4211615 : Blo 984595 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B32492897 : Blo 984595 32492897 := bstep (se 2 (by rfl) ⟨12184836, by rfl⟩ : syracuseStep 32492897 = 24369673) B24369673
theorem B25579135 : Blo 984595 25579135 := bstep (se 1 (by rfl) ⟨19184351, by rfl⟩ : syracuseStep 25579135 = 38368703) B38368703
theorem B2805455 : Blo 984595 2805455 := bstep (se 1 (by rfl) ⟨2104091, by rfl⟩ : syracuseStep 2805455 = 4208183) B4208183
theorem B2215655 : Blo 984595 2215655 := bstep (se 1 (by rfl) ⟨1661741, by rfl⟩ : syracuseStep 2215655 = 3323483) B3323483
theorem B43276355 : Blo 984595 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B2221163 : Blo 984595 2221163 := bstep (se 1 (by rfl) ⟨1665872, by rfl⟩ : syracuseStep 2221163 = 3331745) B3331745
theorem B102364721 : Blo 984595 102364721 := bstep (se 2 (by rfl) ⟨38386770, by rfl⟩ : syracuseStep 102364721 = 76773541) B76773541
theorem B984991 : Blo 984595 984991 := bstep (se 1 (by rfl) ⟨738743, by rfl⟩ : syracuseStep 984991 = 1477487) B1477487
theorem B21661931 : Blo 984595 21661931 := bstep (se 1 (by rfl) ⟨16246448, by rfl⟩ : syracuseStep 21661931 = 32492897) B32492897
theorem B985551 : Blo 984595 985551 := bstep (se 1 (by rfl) ⟨739163, by rfl⟩ : syracuseStep 985551 = 1478327) B1478327
theorem B1870303 : Blo 984595 1870303 := bstep (se 1 (by rfl) ⟨1402727, by rfl⟩ : syracuseStep 1870303 = 2805455) B2805455
theorem B1477103 : Blo 984595 1477103 := bstep (se 1 (by rfl) ⟨1107827, by rfl⟩ : syracuseStep 1477103 = 2215655) B2215655
theorem B986831 : Blo 984595 986831 := bstep (se 1 (by rfl) ⟨740123, by rfl⟩ : syracuseStep 986831 = 1480247) B1480247
theorem B1480775 : Blo 984595 1480775 := bstep (se 1 (by rfl) ⟨1110581, by rfl⟩ : syracuseStep 1480775 = 2221163) B2221163
theorem B136422053 : Blo 984595 136422053 := bstep (se 4 (by rfl) ⟨12789567, by rfl⟩ : syracuseStep 136422053 = 25579135) B25579135
theorem B28850903 : Blo 984595 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B68243147 : Blo 984595 68243147 := bstep (se 1 (by rfl) ⟨51182360, by rfl⟩ : syracuseStep 68243147 = 102364721) B102364721
theorem B3330017 : Blo 984595 3330017 := bstep (se 2 (by rfl) ⟨1248756, by rfl⟩ : syracuseStep 3330017 = 2497513) B2497513
theorem B12801833 : Blo 984595 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B15162335 : Blo 984595 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B11230973 : Blo 984595 11230973 := bstep (se 3 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 11230973 = 4211615) B4211615
theorem B173072969 : Blo 984595 173072969 := bstep (se 2 (by rfl) ⟨64902363, by rfl⟩ : syracuseStep 173072969 = 129804727) B129804727
theorem B10676569 : Blo 984595 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B1666919 : Blo 984595 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B3373535 : Blo 984595 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B984735 : Blo 984595 984735 := bstep (se 1 (by rfl) ⟨738551, by rfl⟩ : syracuseStep 984735 = 1477103) B1477103
theorem B2493737 : Blo 984595 2493737 := bstep (se 2 (by rfl) ⟨935151, by rfl⟩ : syracuseStep 2493737 = 1870303) B1870303
theorem B987183 : Blo 984595 987183 := bstep (se 1 (by rfl) ⟨740387, by rfl⟩ : syracuseStep 987183 = 1480775) B1480775
theorem B115381979 : Blo 984595 115381979 := bstep (se 1 (by rfl) ⟨86536484, by rfl⟩ : syracuseStep 115381979 = 173072969) B173072969
theorem B45495431 : Blo 984595 45495431 := bstep (se 1 (by rfl) ⟨34121573, by rfl⟩ : syracuseStep 45495431 = 68243147) B68243147
theorem B14235425 : Blo 984595 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B8534555 : Blo 984595 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B10108223 : Blo 984595 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B7487315 : Blo 984595 7487315 := bstep (se 1 (by rfl) ⟨5615486, by rfl⟩ : syracuseStep 7487315 = 11230973) B11230973
theorem B90948035 : Blo 984595 90948035 := bstep (se 1 (by rfl) ⟨68211026, by rfl⟩ : syracuseStep 90948035 = 136422053) B136422053
theorem B8996093 : Blo 984595 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B2220011 : Blo 984595 2220011 := bstep (se 1 (by rfl) ⟨1665008, by rfl⟩ : syracuseStep 2220011 = 3330017) B3330017
theorem B57765149 : Blo 984595 57765149 := bstep (se 3 (by rfl) ⟨10830965, by rfl⟩ : syracuseStep 57765149 = 21661931) B21661931
theorem B1111279 : Blo 984595 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B19233935 : Blo 984595 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B5997395 : Blo 984595 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B1480007 : Blo 984595 1480007 := bstep (se 1 (by rfl) ⟨1110005, by rfl⟩ : syracuseStep 1480007 = 2220011) B2220011
theorem B1481705 : Blo 984595 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B38510099 : Blo 984595 38510099 := bstep (se 1 (by rfl) ⟨28882574, by rfl⟩ : syracuseStep 38510099 = 57765149) B57765149
theorem B12822623 : Blo 984595 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B4991543 : Blo 984595 4991543 := bstep (se 1 (by rfl) ⟨3743657, by rfl⟩ : syracuseStep 4991543 = 7487315) B7487315
theorem B60632023 : Blo 984595 60632023 := bstep (se 1 (by rfl) ⟨45474017, by rfl⟩ : syracuseStep 60632023 = 90948035) B90948035
theorem B76921319 : Blo 984595 76921319 := bstep (se 1 (by rfl) ⟨57690989, by rfl⟩ : syracuseStep 76921319 = 115381979) B115381979
theorem B30330287 : Blo 984595 30330287 := bstep (se 1 (by rfl) ⟨22747715, by rfl⟩ : syracuseStep 30330287 = 45495431) B45495431
theorem B9490283 : Blo 984595 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B5689703 : Blo 984595 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B6738815 : Blo 984595 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B1662491 : Blo 984595 1662491 := bstep (se 1 (by rfl) ⟨1246868, by rfl⟩ : syracuseStep 1662491 = 2493737) B2493737
theorem B15172541 : Blo 984595 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B15993053 : Blo 984595 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B20220191 : Blo 984595 20220191 := bstep (se 1 (by rfl) ⟨15165143, by rfl⟩ : syracuseStep 20220191 = 30330287) B30330287
theorem B6326855 : Blo 984595 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B4492543 : Blo 984595 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B986671 : Blo 984595 986671 := bstep (se 1 (by rfl) ⟨740003, by rfl⟩ : syracuseStep 986671 = 1480007) B1480007
theorem B80842697 : Blo 984595 80842697 := bstep (se 2 (by rfl) ⟨30316011, by rfl⟩ : syracuseStep 80842697 = 60632023) B60632023
theorem B987803 : Blo 984595 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B25673399 : Blo 984595 25673399 := bstep (se 1 (by rfl) ⟨19255049, by rfl⟩ : syracuseStep 25673399 = 38510099) B38510099
theorem B3327695 : Blo 984595 3327695 := bstep (se 1 (by rfl) ⟨2495771, by rfl⟩ : syracuseStep 3327695 = 4991543) B4991543
theorem B1108327 : Blo 984595 1108327 := bstep (se 1 (by rfl) ⟨831245, by rfl⟩ : syracuseStep 1108327 = 1662491) B1662491
theorem B8548415 : Blo 984595 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B51280879 : Blo 984595 51280879 := bstep (se 1 (by rfl) ⟨38460659, by rfl⟩ : syracuseStep 51280879 = 76921319) B76921319
theorem B1477769 : Blo 984595 1477769 := bstep (se 2 (by rfl) ⟨554163, by rfl⟩ : syracuseStep 1477769 = 1108327) B1108327
theorem B17115599 : Blo 984595 17115599 := bstep (se 1 (by rfl) ⟨12836699, by rfl⟩ : syracuseStep 17115599 = 25673399) B25673399
theorem B10662035 : Blo 984595 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B13480127 : Blo 984595 13480127 := bstep (se 1 (by rfl) ⟨10110095, by rfl⟩ : syracuseStep 13480127 = 20220191) B20220191
theorem B68374505 : Blo 984595 68374505 := bstep (se 2 (by rfl) ⟨25640439, by rfl⟩ : syracuseStep 68374505 = 51280879) B51280879
theorem B10115027 : Blo 984595 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B2218463 : Blo 984595 2218463 := bstep (se 1 (by rfl) ⟨1663847, by rfl⟩ : syracuseStep 2218463 = 3327695) B3327695
theorem B4217903 : Blo 984595 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B53895131 : Blo 984595 53895131 := bstep (se 1 (by rfl) ⟨40421348, by rfl⟩ : syracuseStep 53895131 = 80842697) B80842697
theorem B5990057 : Blo 984595 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B5698943 : Blo 984595 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B985179 : Blo 984595 985179 := bstep (se 1 (by rfl) ⟨738884, by rfl⟩ : syracuseStep 985179 = 1477769) B1477769
theorem B45583003 : Blo 984595 45583003 := bstep (se 1 (by rfl) ⟨34187252, by rfl⟩ : syracuseStep 45583003 = 68374505) B68374505
theorem B1478975 : Blo 984595 1478975 := bstep (se 1 (by rfl) ⟨1109231, by rfl⟩ : syracuseStep 1478975 = 2218463) B2218463
theorem B11410399 : Blo 984595 11410399 := bstep (se 1 (by rfl) ⟨8557799, by rfl⟩ : syracuseStep 11410399 = 17115599) B17115599
theorem B8986751 : Blo 984595 8986751 := bstep (se 1 (by rfl) ⟨6740063, by rfl⟩ : syracuseStep 8986751 = 13480127) B13480127
theorem B35930087 : Blo 984595 35930087 := bstep (se 1 (by rfl) ⟨26947565, by rfl⟩ : syracuseStep 35930087 = 53895131) B53895131
theorem B28432093 : Blo 984595 28432093 := bstep (se 3 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 28432093 = 10662035) B10662035
theorem B6743351 : Blo 984595 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B2811935 : Blo 984595 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B3993371 : Blo 984595 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B3799295 : Blo 984595 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B985983 : Blo 984595 985983 := bstep (se 1 (by rfl) ⟨739487, by rfl⟩ : syracuseStep 985983 = 1478975) B1478975
theorem B243109349 : Blo 984595 243109349 := bstep (se 4 (by rfl) ⟨22791501, by rfl⟩ : syracuseStep 243109349 = 45583003) B45583003
theorem B60855461 : Blo 984595 60855461 := bstep (se 4 (by rfl) ⟨5705199, by rfl⟩ : syracuseStep 60855461 = 11410399) B11410399
theorem B4495567 : Blo 984595 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B2662247 : Blo 984595 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B2532863 : Blo 984595 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B7498493 : Blo 984595 7498493 := bstep (se 3 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 7498493 = 2811935) B2811935
theorem B5991167 : Blo 984595 5991167 := bstep (se 1 (by rfl) ⟨4493375, by rfl⟩ : syracuseStep 5991167 = 8986751) B8986751
theorem B37909457 : Blo 984595 37909457 := bstep (se 2 (by rfl) ⟨14216046, by rfl⟩ : syracuseStep 37909457 = 28432093) B28432093
theorem B23953391 : Blo 984595 23953391 := bstep (se 1 (by rfl) ⟨17965043, by rfl⟩ : syracuseStep 23953391 = 35930087) B35930087
theorem B162072899 : Blo 984595 162072899 := bstep (se 1 (by rfl) ⟨121554674, by rfl⟩ : syracuseStep 162072899 = 243109349) B243109349
theorem B40570307 : Blo 984595 40570307 := bstep (se 1 (by rfl) ⟨30427730, by rfl⟩ : syracuseStep 40570307 = 60855461) B60855461
theorem B1774831 : Blo 984595 1774831 := bstep (se 1 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 1774831 = 2662247) B2662247
theorem B25272971 : Blo 984595 25272971 := bstep (se 1 (by rfl) ⟨18954728, by rfl⟩ : syracuseStep 25272971 = 37909457) B37909457
theorem B15968927 : Blo 984595 15968927 := bstep (se 1 (by rfl) ⟨11976695, by rfl⟩ : syracuseStep 15968927 = 23953391) B23953391
theorem B1688575 : Blo 984595 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B4998995 : Blo 984595 4998995 := bstep (se 1 (by rfl) ⟨3749246, by rfl⟩ : syracuseStep 4998995 = 7498493) B7498493
theorem B15976445 : Blo 984595 15976445 := bstep (se 3 (by rfl) ⟨2995583, by rfl⟩ : syracuseStep 15976445 = 5991167) B5991167
theorem B5994089 : Blo 984595 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B42603853 : Blo 984595 42603853 := bstep (se 3 (by rfl) ⟨7988222, by rfl⟩ : syracuseStep 42603853 = 15976445) B15976445
theorem B16848647 : Blo 984595 16848647 := bstep (se 1 (by rfl) ⟨12636485, by rfl⟩ : syracuseStep 16848647 = 25272971) B25272971
theorem B2366441 : Blo 984595 2366441 := bstep (se 2 (by rfl) ⟨887415, by rfl⟩ : syracuseStep 2366441 = 1774831) B1774831
theorem B108048599 : Blo 984595 108048599 := bstep (se 1 (by rfl) ⟨81036449, by rfl⟩ : syracuseStep 108048599 = 162072899) B162072899
theorem B27046871 : Blo 984595 27046871 := bstep (se 1 (by rfl) ⟨20285153, by rfl⟩ : syracuseStep 27046871 = 40570307) B40570307
theorem B3332663 : Blo 984595 3332663 := bstep (se 1 (by rfl) ⟨2499497, by rfl⟩ : syracuseStep 3332663 = 4998995) B4998995
theorem B2251433 : Blo 984595 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B10645951 : Blo 984595 10645951 := bstep (se 1 (by rfl) ⟨7984463, by rfl⟩ : syracuseStep 10645951 = 15968927) B15968927
theorem B3996059 : Blo 984595 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B1577627 : Blo 984595 1577627 := bstep (se 1 (by rfl) ⟨1183220, by rfl⟩ : syracuseStep 1577627 = 2366441) B2366441
theorem B14194601 : Blo 984595 14194601 := bstep (se 2 (by rfl) ⟨5322975, by rfl⟩ : syracuseStep 14194601 = 10645951) B10645951
theorem B10656157 : Blo 984595 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B6003821 : Blo 984595 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B72032399 : Blo 984595 72032399 := bstep (se 1 (by rfl) ⟨54024299, by rfl⟩ : syracuseStep 72032399 = 108048599) B108048599
theorem B18031247 : Blo 984595 18031247 := bstep (se 1 (by rfl) ⟨13523435, by rfl⟩ : syracuseStep 18031247 = 27046871) B27046871
theorem B56805137 : Blo 984595 56805137 := bstep (se 2 (by rfl) ⟨21301926, by rfl⟩ : syracuseStep 56805137 = 42603853) B42603853
theorem B11232431 : Blo 984595 11232431 := bstep (se 1 (by rfl) ⟨8424323, by rfl⟩ : syracuseStep 11232431 = 16848647) B16848647
theorem B2221775 : Blo 984595 2221775 := bstep (se 1 (by rfl) ⟨1666331, by rfl⟩ : syracuseStep 2221775 = 3332663) B3332663
theorem B1051751 : Blo 984595 1051751 := bstep (se 1 (by rfl) ⟨788813, by rfl⟩ : syracuseStep 1051751 = 1577627) B1577627
theorem B4002547 : Blo 984595 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B1481183 : Blo 984595 1481183 := bstep (se 1 (by rfl) ⟨1110887, by rfl⟩ : syracuseStep 1481183 = 2221775) B2221775
theorem B48021599 : Blo 984595 48021599 := bstep (se 1 (by rfl) ⟨36016199, by rfl⟩ : syracuseStep 48021599 = 72032399) B72032399
theorem B7488287 : Blo 984595 7488287 := bstep (se 1 (by rfl) ⟨5616215, by rfl⟩ : syracuseStep 7488287 = 11232431) B11232431
theorem B14208209 : Blo 984595 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B37870091 : Blo 984595 37870091 := bstep (se 1 (by rfl) ⟨28402568, by rfl⟩ : syracuseStep 37870091 = 56805137) B56805137
theorem B9463067 : Blo 984595 9463067 := bstep (se 1 (by rfl) ⟨7097300, by rfl⟩ : syracuseStep 9463067 = 14194601) B14194601
theorem B12020831 : Blo 984595 12020831 := bstep (se 1 (by rfl) ⟨9015623, by rfl⟩ : syracuseStep 12020831 = 18031247) B18031247
theorem B32014399 : Blo 984595 32014399 := bstep (se 1 (by rfl) ⟨24010799, by rfl⟩ : syracuseStep 32014399 = 48021599) B48021599
theorem B9472139 : Blo 984595 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B987455 : Blo 984595 987455 := bstep (se 1 (by rfl) ⟨740591, by rfl⟩ : syracuseStep 987455 = 1481183) B1481183
theorem B4992191 : Blo 984595 4992191 := bstep (se 1 (by rfl) ⟨3744143, by rfl⟩ : syracuseStep 4992191 = 7488287) B7488287
theorem B25246727 : Blo 984595 25246727 := bstep (se 1 (by rfl) ⟨18935045, by rfl⟩ : syracuseStep 25246727 = 37870091) B37870091
theorem B6308711 : Blo 984595 6308711 := bstep (se 1 (by rfl) ⟨4731533, by rfl⟩ : syracuseStep 6308711 = 9463067) B9463067
theorem B8013887 : Blo 984595 8013887 := bstep (se 1 (by rfl) ⟨6010415, by rfl⟩ : syracuseStep 8013887 = 12020831) B12020831
theorem B2804669 : Blo 984595 2804669 := bstep (se 3 (by rfl) ⟨525875, by rfl⟩ : syracuseStep 2804669 = 1051751) B1051751
theorem B5336729 : Blo 984595 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B5342591 : Blo 984595 5342591 := bstep (se 1 (by rfl) ⟨4006943, by rfl⟩ : syracuseStep 5342591 = 8013887) B8013887
theorem B1869779 : Blo 984595 1869779 := bstep (se 1 (by rfl) ⟨1402334, by rfl⟩ : syracuseStep 1869779 = 2804669) B2804669
theorem B4205807 : Blo 984595 4205807 := bstep (se 1 (by rfl) ⟨3154355, by rfl⟩ : syracuseStep 4205807 = 6308711) B6308711
theorem B3328127 : Blo 984595 3328127 := bstep (se 1 (by rfl) ⟨2496095, by rfl⟩ : syracuseStep 3328127 = 4992191) B4992191
theorem B3557819 : Blo 984595 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B16831151 : Blo 984595 16831151 := bstep (se 1 (by rfl) ⟨12623363, by rfl⟩ : syracuseStep 16831151 = 25246727) B25246727
theorem B42685865 : Blo 984595 42685865 := bstep (se 2 (by rfl) ⟨16007199, by rfl⟩ : syracuseStep 42685865 = 32014399) B32014399
theorem B6314759 : Blo 984595 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1246519 : Blo 984595 1246519 := bstep (se 1 (by rfl) ⟨934889, by rfl⟩ : syracuseStep 1246519 = 1869779) B1869779
theorem B2371879 : Blo 984595 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B11220767 : Blo 984595 11220767 := bstep (se 1 (by rfl) ⟨8415575, by rfl⟩ : syracuseStep 11220767 = 16831151) B16831151
theorem B28457243 : Blo 984595 28457243 := bstep (se 1 (by rfl) ⟨21342932, by rfl⟩ : syracuseStep 28457243 = 42685865) B42685865
theorem B4209839 : Blo 984595 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B2803871 : Blo 984595 2803871 := bstep (se 1 (by rfl) ⟨2102903, by rfl⟩ : syracuseStep 2803871 = 4205807) B4205807
theorem B3561727 : Blo 984595 3561727 := bstep (se 1 (by rfl) ⟨2671295, by rfl⟩ : syracuseStep 3561727 = 5342591) B5342591
theorem B2218751 : Blo 984595 2218751 := bstep (se 1 (by rfl) ⟨1664063, by rfl⟩ : syracuseStep 2218751 = 3328127) B3328127
theorem B1869247 : Blo 984595 1869247 := bstep (se 1 (by rfl) ⟨1401935, by rfl⟩ : syracuseStep 1869247 = 2803871) B2803871
theorem B1479167 : Blo 984595 1479167 := bstep (se 1 (by rfl) ⟨1109375, by rfl⟩ : syracuseStep 1479167 = 2218751) B2218751
theorem B7480511 : Blo 984595 7480511 := bstep (se 1 (by rfl) ⟨5610383, by rfl⟩ : syracuseStep 7480511 = 11220767) B11220767
theorem B3162505 : Blo 984595 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B2806559 : Blo 984595 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B1662025 : Blo 984595 1662025 := bstep (se 2 (by rfl) ⟨623259, by rfl⟩ : syracuseStep 1662025 = 1246519) B1246519
theorem B4748969 : Blo 984595 4748969 := bstep (se 2 (by rfl) ⟨1780863, by rfl⟩ : syracuseStep 4748969 = 3561727) B3561727
theorem B18971495 : Blo 984595 18971495 := bstep (se 1 (by rfl) ⟨14228621, by rfl⟩ : syracuseStep 18971495 = 28457243) B28457243
theorem B2492329 : Blo 984595 2492329 := bstep (se 2 (by rfl) ⟨934623, by rfl⟩ : syracuseStep 2492329 = 1869247) B1869247
theorem B986111 : Blo 984595 986111 := bstep (se 1 (by rfl) ⟨739583, by rfl⟩ : syracuseStep 986111 = 1479167) B1479167
theorem B1871039 : Blo 984595 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B4987007 : Blo 984595 4987007 := bstep (se 1 (by rfl) ⟨3740255, by rfl⟩ : syracuseStep 4987007 = 7480511) B7480511
theorem B3165979 : Blo 984595 3165979 := bstep (se 1 (by rfl) ⟨2374484, by rfl⟩ : syracuseStep 3165979 = 4748969) B4748969
theorem B2216033 : Blo 984595 2216033 := bstep (se 2 (by rfl) ⟨831012, by rfl⟩ : syracuseStep 2216033 = 1662025) B1662025
theorem B4216673 : Blo 984595 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B12647663 : Blo 984595 12647663 := bstep (se 1 (by rfl) ⟨9485747, by rfl⟩ : syracuseStep 12647663 = 18971495) B18971495
theorem B1477355 : Blo 984595 1477355 := bstep (se 1 (by rfl) ⟨1108016, by rfl⟩ : syracuseStep 1477355 = 2216033) B2216033
theorem B4989437 : Blo 984595 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B8431775 : Blo 984595 8431775 := bstep (se 1 (by rfl) ⟨6323831, by rfl⟩ : syracuseStep 8431775 = 12647663) B12647663
theorem B3323105 : Blo 984595 3323105 := bstep (se 2 (by rfl) ⟨1246164, by rfl⟩ : syracuseStep 3323105 = 2492329) B2492329
theorem B3324671 : Blo 984595 3324671 := bstep (se 1 (by rfl) ⟨2493503, by rfl⟩ : syracuseStep 3324671 = 4987007) B4987007
theorem B2811115 : Blo 984595 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B4221305 : Blo 984595 4221305 := bstep (se 2 (by rfl) ⟨1582989, by rfl⟩ : syracuseStep 4221305 = 3165979) B3165979
theorem B984903 : Blo 984595 984903 := bstep (se 1 (by rfl) ⟨738677, by rfl⟩ : syracuseStep 984903 = 1477355) B1477355
theorem B3748153 : Blo 984595 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B3326291 : Blo 984595 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B5621183 : Blo 984595 5621183 := bstep (se 1 (by rfl) ⟨4215887, by rfl⟩ : syracuseStep 5621183 = 8431775) B8431775
theorem B2215403 : Blo 984595 2215403 := bstep (se 1 (by rfl) ⟨1661552, by rfl⟩ : syracuseStep 2215403 = 3323105) B3323105
theorem B2216447 : Blo 984595 2216447 := bstep (se 1 (by rfl) ⟨1662335, by rfl⟩ : syracuseStep 2216447 = 3324671) B3324671
theorem B2814203 : Blo 984595 2814203 := bstep (se 1 (by rfl) ⟨2110652, by rfl⟩ : syracuseStep 2814203 = 4221305) B4221305
theorem B1476935 : Blo 984595 1476935 := bstep (se 1 (by rfl) ⟨1107701, by rfl⟩ : syracuseStep 1476935 = 2215403) B2215403
theorem B1477631 : Blo 984595 1477631 := bstep (se 1 (by rfl) ⟨1108223, by rfl⟩ : syracuseStep 1477631 = 2216447) B2216447
theorem B1876135 : Blo 984595 1876135 := bstep (se 1 (by rfl) ⟨1407101, by rfl⟩ : syracuseStep 1876135 = 2814203) B2814203
theorem B3747455 : Blo 984595 3747455 := bstep (se 1 (by rfl) ⟨2810591, by rfl⟩ : syracuseStep 3747455 = 5621183) B5621183
theorem B4997537 : Blo 984595 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B2217527 : Blo 984595 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B984623 : Blo 984595 984623 := bstep (se 1 (by rfl) ⟨738467, by rfl⟩ : syracuseStep 984623 = 1476935) B1476935
theorem B985087 : Blo 984595 985087 := bstep (se 1 (by rfl) ⟨738815, by rfl⟩ : syracuseStep 985087 = 1477631) B1477631
theorem B1478351 : Blo 984595 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527
theorem B2498303 : Blo 984595 2498303 := bstep (se 1 (by rfl) ⟨1873727, by rfl⟩ : syracuseStep 2498303 = 3747455) B3747455
theorem B2501513 : Blo 984595 2501513 := bstep (se 2 (by rfl) ⟨938067, by rfl⟩ : syracuseStep 2501513 = 1876135) B1876135
theorem B3331691 : Blo 984595 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B985567 : Blo 984595 985567 := bstep (se 1 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 985567 = 1478351) B1478351
theorem B2221127 : Blo 984595 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B1665535 : Blo 984595 1665535 := bstep (se 1 (by rfl) ⟨1249151, by rfl⟩ : syracuseStep 1665535 = 2498303) B2498303
theorem B1667675 : Blo 984595 1667675 := bstep (se 1 (by rfl) ⟨1250756, by rfl⟩ : syracuseStep 1667675 = 2501513) B2501513
theorem B1480751 : Blo 984595 1480751 := bstep (se 1 (by rfl) ⟨1110563, by rfl⟩ : syracuseStep 1480751 = 2221127) B2221127
theorem B2220713 : Blo 984595 2220713 := bstep (se 2 (by rfl) ⟨832767, by rfl⟩ : syracuseStep 2220713 = 1665535) B1665535
theorem B1111783 : Blo 984595 1111783 := bstep (se 1 (by rfl) ⟨833837, by rfl⟩ : syracuseStep 1111783 = 1667675) B1667675
theorem B987167 : Blo 984595 987167 := bstep (se 1 (by rfl) ⟨740375, by rfl⟩ : syracuseStep 987167 = 1480751) B1480751
theorem B1480475 : Blo 984595 1480475 := bstep (se 1 (by rfl) ⟨1110356, by rfl⟩ : syracuseStep 1480475 = 2220713) B2220713
theorem B1482377 : Blo 984595 1482377 := bstep (se 2 (by rfl) ⟨555891, by rfl⟩ : syracuseStep 1482377 = 1111783) B1111783
theorem B986983 : Blo 984595 986983 := bstep (se 1 (by rfl) ⟨740237, by rfl⟩ : syracuseStep 986983 = 1480475) B1480475
theorem B988251 : Blo 984595 988251 := bstep (se 1 (by rfl) ⟨741188, by rfl⟩ : syracuseStep 988251 = 1482377) B1482377

theorem C0 (j : ℕ) (h1 : 246148 ≤ j) (h2 : j ≤ 246847) : Blo 984595 (4 * j + 3) := by
  interval_cases j
  · exact B984595
  · exact B984599
  · exact B984603
  · exact B984607
  · exact B984611
  · exact B984615
  · exact B984619
  · exact B984623
  · exact B984627
  · exact B984631
  · exact B984635
  · exact B984639
  · exact B984643
  · exact B984647
  · exact B984651
  · exact B984655
  · exact B984659
  · exact B984663
  · exact B984667
  · exact B984671
  · exact B984675
  · exact B984679
  · exact B984683
  · exact B984687
  · exact B984691
  · exact B984695
  · exact B984699
  · exact B984703
  · exact B984707
  · exact B984711
  · exact B984715
  · exact B984719
  · exact B984723
  · exact B984727
  · exact B984731
  · exact B984735
  · exact B984739
  · exact B984743
  · exact B984747
  · exact B984751
  · exact B984755
  · exact B984759
  · exact B984763
  · exact B984767
  · exact B984771
  · exact B984775
  · exact B984779
  · exact B984783
  · exact B984787
  · exact B984791
  · exact B984795
  · exact B984799
  · exact B984803
  · exact B984807
  · exact B984811
  · exact B984815
  · exact B984819
  · exact B984823
  · exact B984827
  · exact B984831
  · exact B984835
  · exact B984839
  · exact B984843
  · exact B984847
  · exact B984851
  · exact B984855
  · exact B984859
  · exact B984863
  · exact B984867
  · exact B984871
  · exact B984875
  · exact B984879
  · exact B984883
  · exact B984887
  · exact B984891
  · exact B984895
  · exact B984899
  · exact B984903
  · exact B984907
  · exact B984911
  · exact B984915
  · exact B984919
  · exact B984923
  · exact B984927
  · exact B984931
  · exact B984935
  · exact B984939
  · exact B984943
  · exact B984947
  · exact B984951
  · exact B984955
  · exact B984959
  · exact B984963
  · exact B984967
  · exact B984971
  · exact B984975
  · exact B984979
  · exact B984983
  · exact B984987
  · exact B984991
  · exact B984995
  · exact B984999
  · exact B985003
  · exact B985007
  · exact B985011
  · exact B985015
  · exact B985019
  · exact B985023
  · exact B985027
  · exact B985031
  · exact B985035
  · exact B985039
  · exact B985043
  · exact B985047
  · exact B985051
  · exact B985055
  · exact B985059
  · exact B985063
  · exact B985067
  · exact B985071
  · exact B985075
  · exact B985079
  · exact B985083
  · exact B985087
  · exact B985091
  · exact B985095
  · exact B985099
  · exact B985103
  · exact B985107
  · exact B985111
  · exact B985115
  · exact B985119
  · exact B985123
  · exact B985127
  · exact B985131
  · exact B985135
  · exact B985139
  · exact B985143
  · exact B985147
  · exact B985151
  · exact B985155
  · exact B985159
  · exact B985163
  · exact B985167
  · exact B985171
  · exact B985175
  · exact B985179
  · exact B985183
  · exact B985187
  · exact B985191
  · exact B985195
  · exact B985199
  · exact B985203
  · exact B985207
  · exact B985211
  · exact B985215
  · exact B985219
  · exact B985223
  · exact B985227
  · exact B985231
  · exact B985235
  · exact B985239
  · exact B985243
  · exact B985247
  · exact B985251
  · exact B985255
  · exact B985259
  · exact B985263
  · exact B985267
  · exact B985271
  · exact B985275
  · exact B985279
  · exact B985283
  · exact B985287
  · exact B985291
  · exact B985295
  · exact B985299
  · exact B985303
  · exact B985307
  · exact B985311
  · exact B985315
  · exact B985319
  · exact B985323
  · exact B985327
  · exact B985331
  · exact B985335
  · exact B985339
  · exact B985343
  · exact B985347
  · exact B985351
  · exact B985355
  · exact B985359
  · exact B985363
  · exact B985367
  · exact B985371
  · exact B985375
  · exact B985379
  · exact B985383
  · exact B985387
  · exact B985391
  · exact B985395
  · exact B985399
  · exact B985403
  · exact B985407
  · exact B985411
  · exact B985415
  · exact B985419
  · exact B985423
  · exact B985427
  · exact B985431
  · exact B985435
  · exact B985439
  · exact B985443
  · exact B985447
  · exact B985451
  · exact B985455
  · exact B985459
  · exact B985463
  · exact B985467
  · exact B985471
  · exact B985475
  · exact B985479
  · exact B985483
  · exact B985487
  · exact B985491
  · exact B985495
  · exact B985499
  · exact B985503
  · exact B985507
  · exact B985511
  · exact B985515
  · exact B985519
  · exact B985523
  · exact B985527
  · exact B985531
  · exact B985535
  · exact B985539
  · exact B985543
  · exact B985547
  · exact B985551
  · exact B985555
  · exact B985559
  · exact B985563
  · exact B985567
  · exact B985571
  · exact B985575
  · exact B985579
  · exact B985583
  · exact B985587
  · exact B985591
  · exact B985595
  · exact B985599
  · exact B985603
  · exact B985607
  · exact B985611
  · exact B985615
  · exact B985619
  · exact B985623
  · exact B985627
  · exact B985631
  · exact B985635
  · exact B985639
  · exact B985643
  · exact B985647
  · exact B985651
  · exact B985655
  · exact B985659
  · exact B985663
  · exact B985667
  · exact B985671
  · exact B985675
  · exact B985679
  · exact B985683
  · exact B985687
  · exact B985691
  · exact B985695
  · exact B985699
  · exact B985703
  · exact B985707
  · exact B985711
  · exact B985715
  · exact B985719
  · exact B985723
  · exact B985727
  · exact B985731
  · exact B985735
  · exact B985739
  · exact B985743
  · exact B985747
  · exact B985751
  · exact B985755
  · exact B985759
  · exact B985763
  · exact B985767
  · exact B985771
  · exact B985775
  · exact B985779
  · exact B985783
  · exact B985787
  · exact B985791
  · exact B985795
  · exact B985799
  · exact B985803
  · exact B985807
  · exact B985811
  · exact B985815
  · exact B985819
  · exact B985823
  · exact B985827
  · exact B985831
  · exact B985835
  · exact B985839
  · exact B985843
  · exact B985847
  · exact B985851
  · exact B985855
  · exact B985859
  · exact B985863
  · exact B985867
  · exact B985871
  · exact B985875
  · exact B985879
  · exact B985883
  · exact B985887
  · exact B985891
  · exact B985895
  · exact B985899
  · exact B985903
  · exact B985907
  · exact B985911
  · exact B985915
  · exact B985919
  · exact B985923
  · exact B985927
  · exact B985931
  · exact B985935
  · exact B985939
  · exact B985943
  · exact B985947
  · exact B985951
  · exact B985955
  · exact B985959
  · exact B985963
  · exact B985967
  · exact B985971
  · exact B985975
  · exact B985979
  · exact B985983
  · exact B985987
  · exact B985991
  · exact B985995
  · exact B985999
  · exact B986003
  · exact B986007
  · exact B986011
  · exact B986015
  · exact B986019
  · exact B986023
  · exact B986027
  · exact B986031
  · exact B986035
  · exact B986039
  · exact B986043
  · exact B986047
  · exact B986051
  · exact B986055
  · exact B986059
  · exact B986063
  · exact B986067
  · exact B986071
  · exact B986075
  · exact B986079
  · exact B986083
  · exact B986087
  · exact B986091
  · exact B986095
  · exact B986099
  · exact B986103
  · exact B986107
  · exact B986111
  · exact B986115
  · exact B986119
  · exact B986123
  · exact B986127
  · exact B986131
  · exact B986135
  · exact B986139
  · exact B986143
  · exact B986147
  · exact B986151
  · exact B986155
  · exact B986159
  · exact B986163
  · exact B986167
  · exact B986171
  · exact B986175
  · exact B986179
  · exact B986183
  · exact B986187
  · exact B986191
  · exact B986195
  · exact B986199
  · exact B986203
  · exact B986207
  · exact B986211
  · exact B986215
  · exact B986219
  · exact B986223
  · exact B986227
  · exact B986231
  · exact B986235
  · exact B986239
  · exact B986243
  · exact B986247
  · exact B986251
  · exact B986255
  · exact B986259
  · exact B986263
  · exact B986267
  · exact B986271
  · exact B986275
  · exact B986279
  · exact B986283
  · exact B986287
  · exact B986291
  · exact B986295
  · exact B986299
  · exact B986303
  · exact B986307
  · exact B986311
  · exact B986315
  · exact B986319
  · exact B986323
  · exact B986327
  · exact B986331
  · exact B986335
  · exact B986339
  · exact B986343
  · exact B986347
  · exact B986351
  · exact B986355
  · exact B986359
  · exact B986363
  · exact B986367
  · exact B986371
  · exact B986375
  · exact B986379
  · exact B986383
  · exact B986387
  · exact B986391
  · exact B986395
  · exact B986399
  · exact B986403
  · exact B986407
  · exact B986411
  · exact B986415
  · exact B986419
  · exact B986423
  · exact B986427
  · exact B986431
  · exact B986435
  · exact B986439
  · exact B986443
  · exact B986447
  · exact B986451
  · exact B986455
  · exact B986459
  · exact B986463
  · exact B986467
  · exact B986471
  · exact B986475
  · exact B986479
  · exact B986483
  · exact B986487
  · exact B986491
  · exact B986495
  · exact B986499
  · exact B986503
  · exact B986507
  · exact B986511
  · exact B986515
  · exact B986519
  · exact B986523
  · exact B986527
  · exact B986531
  · exact B986535
  · exact B986539
  · exact B986543
  · exact B986547
  · exact B986551
  · exact B986555
  · exact B986559
  · exact B986563
  · exact B986567
  · exact B986571
  · exact B986575
  · exact B986579
  · exact B986583
  · exact B986587
  · exact B986591
  · exact B986595
  · exact B986599
  · exact B986603
  · exact B986607
  · exact B986611
  · exact B986615
  · exact B986619
  · exact B986623
  · exact B986627
  · exact B986631
  · exact B986635
  · exact B986639
  · exact B986643
  · exact B986647
  · exact B986651
  · exact B986655
  · exact B986659
  · exact B986663
  · exact B986667
  · exact B986671
  · exact B986675
  · exact B986679
  · exact B986683
  · exact B986687
  · exact B986691
  · exact B986695
  · exact B986699
  · exact B986703
  · exact B986707
  · exact B986711
  · exact B986715
  · exact B986719
  · exact B986723
  · exact B986727
  · exact B986731
  · exact B986735
  · exact B986739
  · exact B986743
  · exact B986747
  · exact B986751
  · exact B986755
  · exact B986759
  · exact B986763
  · exact B986767
  · exact B986771
  · exact B986775
  · exact B986779
  · exact B986783
  · exact B986787
  · exact B986791
  · exact B986795
  · exact B986799
  · exact B986803
  · exact B986807
  · exact B986811
  · exact B986815
  · exact B986819
  · exact B986823
  · exact B986827
  · exact B986831
  · exact B986835
  · exact B986839
  · exact B986843
  · exact B986847
  · exact B986851
  · exact B986855
  · exact B986859
  · exact B986863
  · exact B986867
  · exact B986871
  · exact B986875
  · exact B986879
  · exact B986883
  · exact B986887
  · exact B986891
  · exact B986895
  · exact B986899
  · exact B986903
  · exact B986907
  · exact B986911
  · exact B986915
  · exact B986919
  · exact B986923
  · exact B986927
  · exact B986931
  · exact B986935
  · exact B986939
  · exact B986943
  · exact B986947
  · exact B986951
  · exact B986955
  · exact B986959
  · exact B986963
  · exact B986967
  · exact B986971
  · exact B986975
  · exact B986979
  · exact B986983
  · exact B986987
  · exact B986991
  · exact B986995
  · exact B986999
  · exact B987003
  · exact B987007
  · exact B987011
  · exact B987015
  · exact B987019
  · exact B987023
  · exact B987027
  · exact B987031
  · exact B987035
  · exact B987039
  · exact B987043
  · exact B987047
  · exact B987051
  · exact B987055
  · exact B987059
  · exact B987063
  · exact B987067
  · exact B987071
  · exact B987075
  · exact B987079
  · exact B987083
  · exact B987087
  · exact B987091
  · exact B987095
  · exact B987099
  · exact B987103
  · exact B987107
  · exact B987111
  · exact B987115
  · exact B987119
  · exact B987123
  · exact B987127
  · exact B987131
  · exact B987135
  · exact B987139
  · exact B987143
  · exact B987147
  · exact B987151
  · exact B987155
  · exact B987159
  · exact B987163
  · exact B987167
  · exact B987171
  · exact B987175
  · exact B987179
  · exact B987183
  · exact B987187
  · exact B987191
  · exact B987195
  · exact B987199
  · exact B987203
  · exact B987207
  · exact B987211
  · exact B987215
  · exact B987219
  · exact B987223
  · exact B987227
  · exact B987231
  · exact B987235
  · exact B987239
  · exact B987243
  · exact B987247
  · exact B987251
  · exact B987255
  · exact B987259
  · exact B987263
  · exact B987267
  · exact B987271
  · exact B987275
  · exact B987279
  · exact B987283
  · exact B987287
  · exact B987291
  · exact B987295
  · exact B987299
  · exact B987303
  · exact B987307
  · exact B987311
  · exact B987315
  · exact B987319
  · exact B987323
  · exact B987327
  · exact B987331
  · exact B987335
  · exact B987339
  · exact B987343
  · exact B987347
  · exact B987351
  · exact B987355
  · exact B987359
  · exact B987363
  · exact B987367
  · exact B987371
  · exact B987375
  · exact B987379
  · exact B987383
  · exact B987387
  · exact B987391

theorem C1 (j : ℕ) (h1 : 246848 ≤ j) (h2 : j ≤ 247148) : Blo 984595 (4 * j + 3) := by
  interval_cases j
  · exact B987395
  · exact B987399
  · exact B987403
  · exact B987407
  · exact B987411
  · exact B987415
  · exact B987419
  · exact B987423
  · exact B987427
  · exact B987431
  · exact B987435
  · exact B987439
  · exact B987443
  · exact B987447
  · exact B987451
  · exact B987455
  · exact B987459
  · exact B987463
  · exact B987467
  · exact B987471
  · exact B987475
  · exact B987479
  · exact B987483
  · exact B987487
  · exact B987491
  · exact B987495
  · exact B987499
  · exact B987503
  · exact B987507
  · exact B987511
  · exact B987515
  · exact B987519
  · exact B987523
  · exact B987527
  · exact B987531
  · exact B987535
  · exact B987539
  · exact B987543
  · exact B987547
  · exact B987551
  · exact B987555
  · exact B987559
  · exact B987563
  · exact B987567
  · exact B987571
  · exact B987575
  · exact B987579
  · exact B987583
  · exact B987587
  · exact B987591
  · exact B987595
  · exact B987599
  · exact B987603
  · exact B987607
  · exact B987611
  · exact B987615
  · exact B987619
  · exact B987623
  · exact B987627
  · exact B987631
  · exact B987635
  · exact B987639
  · exact B987643
  · exact B987647
  · exact B987651
  · exact B987655
  · exact B987659
  · exact B987663
  · exact B987667
  · exact B987671
  · exact B987675
  · exact B987679
  · exact B987683
  · exact B987687
  · exact B987691
  · exact B987695
  · exact B987699
  · exact B987703
  · exact B987707
  · exact B987711
  · exact B987715
  · exact B987719
  · exact B987723
  · exact B987727
  · exact B987731
  · exact B987735
  · exact B987739
  · exact B987743
  · exact B987747
  · exact B987751
  · exact B987755
  · exact B987759
  · exact B987763
  · exact B987767
  · exact B987771
  · exact B987775
  · exact B987779
  · exact B987783
  · exact B987787
  · exact B987791
  · exact B987795
  · exact B987799
  · exact B987803
  · exact B987807
  · exact B987811
  · exact B987815
  · exact B987819
  · exact B987823
  · exact B987827
  · exact B987831
  · exact B987835
  · exact B987839
  · exact B987843
  · exact B987847
  · exact B987851
  · exact B987855
  · exact B987859
  · exact B987863
  · exact B987867
  · exact B987871
  · exact B987875
  · exact B987879
  · exact B987883
  · exact B987887
  · exact B987891
  · exact B987895
  · exact B987899
  · exact B987903
  · exact B987907
  · exact B987911
  · exact B987915
  · exact B987919
  · exact B987923
  · exact B987927
  · exact B987931
  · exact B987935
  · exact B987939
  · exact B987943
  · exact B987947
  · exact B987951
  · exact B987955
  · exact B987959
  · exact B987963
  · exact B987967
  · exact B987971
  · exact B987975
  · exact B987979
  · exact B987983
  · exact B987987
  · exact B987991
  · exact B987995
  · exact B987999
  · exact B988003
  · exact B988007
  · exact B988011
  · exact B988015
  · exact B988019
  · exact B988023
  · exact B988027
  · exact B988031
  · exact B988035
  · exact B988039
  · exact B988043
  · exact B988047
  · exact B988051
  · exact B988055
  · exact B988059
  · exact B988063
  · exact B988067
  · exact B988071
  · exact B988075
  · exact B988079
  · exact B988083
  · exact B988087
  · exact B988091
  · exact B988095
  · exact B988099
  · exact B988103
  · exact B988107
  · exact B988111
  · exact B988115
  · exact B988119
  · exact B988123
  · exact B988127
  · exact B988131
  · exact B988135
  · exact B988139
  · exact B988143
  · exact B988147
  · exact B988151
  · exact B988155
  · exact B988159
  · exact B988163
  · exact B988167
  · exact B988171
  · exact B988175
  · exact B988179
  · exact B988183
  · exact B988187
  · exact B988191
  · exact B988195
  · exact B988199
  · exact B988203
  · exact B988207
  · exact B988211
  · exact B988215
  · exact B988219
  · exact B988223
  · exact B988227
  · exact B988231
  · exact B988235
  · exact B988239
  · exact B988243
  · exact B988247
  · exact B988251
  · exact B988255
  · exact B988259
  · exact B988263
  · exact B988267
  · exact B988271
  · exact B988275
  · exact B988279
  · exact B988283
  · exact B988287
  · exact B988291
  · exact B988295
  · exact B988299
  · exact B988303
  · exact B988307
  · exact B988311
  · exact B988315
  · exact B988319
  · exact B988323
  · exact B988327
  · exact B988331
  · exact B988335
  · exact B988339
  · exact B988343
  · exact B988347
  · exact B988351
  · exact B988355
  · exact B988359
  · exact B988363
  · exact B988367
  · exact B988371
  · exact B988375
  · exact B988379
  · exact B988383
  · exact B988387
  · exact B988391
  · exact B988395
  · exact B988399
  · exact B988403
  · exact B988407
  · exact B988411
  · exact B988415
  · exact B988419
  · exact B988423
  · exact B988427
  · exact B988431
  · exact B988435
  · exact B988439
  · exact B988443
  · exact B988447
  · exact B988451
  · exact B988455
  · exact B988459
  · exact B988463
  · exact B988467
  · exact B988471
  · exact B988475
  · exact B988479
  · exact B988483
  · exact B988487
  · exact B988491
  · exact B988495
  · exact B988499
  · exact B988503
  · exact B988507
  · exact B988511
  · exact B988515
  · exact B988519
  · exact B988523
  · exact B988527
  · exact B988531
  · exact B988535
  · exact B988539
  · exact B988543
  · exact B988547
  · exact B988551
  · exact B988555
  · exact B988559
  · exact B988563
  · exact B988567
  · exact B988571
  · exact B988575
  · exact B988579
  · exact B988583
  · exact B988587
  · exact B988591
  · exact B988595

theorem solution (m : ℕ) (hlo : 984595 ≤ m) (hhi : m ≤ 988595) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 246148 ≤ j := by omega
    have hj2 : j ≤ 247148 := by omega
    have hb : Blo 984595 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 246848 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
