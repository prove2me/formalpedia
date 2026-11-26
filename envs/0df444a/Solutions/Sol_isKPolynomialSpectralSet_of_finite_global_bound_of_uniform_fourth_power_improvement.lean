-- Prove2me | solution 1 for isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:58.599554+00:00
-- url     : https://prove2.me/submissions/5fdcbbfb-fac1-4bbc-af4d-7738d2d050a4

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (S : Set ℂ) (hspectrum : spectrum ℂ A ⊆ S)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p S)
    (hfour : ∀ K : ℝ, 0 ≤ K →
      (∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p S) →
      ∀ p : Polynomial ℂ,
        ‖Polynomial.aeval A p‖ ^ 4 ≤
          (2 * K ^ 3 + K ^ 2) *
            polynomialSupNorm p S ^ 4) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) S := by
  let m : Polynomial ℂ → ℝ := fun p ↦
    polynomialSupNorm p S
  let ratio : Polynomial ℂ → ℝ := fun p ↦
    if m p = 0 then 0 else ‖Polynomial.aeval A p‖ / m p
  let ratios : Set ℝ := Set.range ratio
  let K : ℝ := sSup ratios
  obtain ⟨K₀, hK₀, hcalc₀⟩ := hfinite
  have hm_nonneg (p : Polynomial ℂ) : 0 ≤ m p := by
    exact polynomialSupNorm_nonneg p S
  have hratio_nonneg (p : Polynomial ℂ) : 0 ≤ ratio p := by
    by_cases hp : m p = 0
    · simp only [ratio, hp, if_pos, le_rfl]
    · simp only [ratio, hp, if_false]
      exact div_nonneg (norm_nonneg _) (hm_nonneg p)
  have hratios_nonempty : ratios.Nonempty := Set.range_nonempty ratio
  have hratios_bdd : BddAbove ratios := by
    refine ⟨K₀, ?_⟩
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    by_cases hp : m p = 0
    · simp only [ratio, hp, if_pos]
      exact hK₀
    · have hmp : 0 < m p := lt_of_le_of_ne (hm_nonneg p) (Ne.symm hp)
      simp only [ratio, hp, if_false]
      exact (div_le_iff₀ hmp).2 (hcalc₀ p)
  have hratio_le (p : Polynomial ℂ) : ratio p ≤ K := by
    exact le_csSup hratios_bdd (Set.mem_range_self p)
  have hK : 0 ≤ K := by
    exact (hratio_nonneg 0).trans (hratio_le 0)
  have hcalc : ∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤ K * m p := by
    intro p
    by_cases hp : m p = 0
    · have hcalc₀' : ‖Polynomial.aeval A p‖ ≤ K₀ * m p := by
        simpa only [m] using hcalc₀ p
      have hnorm : ‖Polynomial.aeval A p‖ = 0 := by
        apply le_antisymm
        · rw [hp, mul_zero] at hcalc₀'
          exact hcalc₀'
        · exact norm_nonneg _
      rw [hp, mul_zero, hnorm]
    · have hmp : 0 < m p := lt_of_le_of_ne (hm_nonneg p) (Ne.symm hp)
      apply (div_le_iff₀ hmp).1
      simpa only [ratio, hp, if_false] using hratio_le p
  let C : ℝ := 2 * K ^ 3 + K ^ 2
  let B : ℝ := Real.sqrt (Real.sqrt C)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBpow : B ^ 4 = C := by
    calc
      B ^ 4 = (Real.sqrt C) ^ 2 := by
        dsimp only [B]
        rw [show Real.sqrt (Real.sqrt C) ^ 4 =
          (Real.sqrt (Real.sqrt C) ^ 2) ^ 2 by ring,
          Real.sq_sqrt (Real.sqrt_nonneg C)]
      _ = C := Real.sq_sqrt hC
  have hratios_le_B : ∀ y ∈ ratios, y ≤ B := by
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    by_cases hp : m p = 0
    · simp only [ratio, hp, if_pos]
      exact hB
    · have hmp : 0 < m p := lt_of_le_of_ne (hm_nonneg p) (Ne.symm hp)
      have hpow : ratio p ^ 4 ≤ C := by
        calc
          ratio p ^ 4 = ‖Polynomial.aeval A p‖ ^ 4 / m p ^ 4 := by
            simp only [ratio, hp, if_false, div_pow]
          _ ≤ C := (div_le_iff₀ (pow_pos hmp 4)).2 (hfour K hK hcalc p)
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hB
      rwa [hBpow]
  have hKleB : K ≤ B := csSup_le hratios_nonempty hratios_le_B
  have hKfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2 := by
    change K ^ 4 ≤ C
    calc
      K ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hK hKleB 4
      _ = C := hBpow
  refine ⟨hspectrum, ?_⟩
  intro p
  have hfixed :=
    le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq hK hKfour
  exact (hcalc p).trans (mul_le_mul_of_nonneg_right hfixed
    (polynomialSupNorm_nonneg p S))
