-- Prove2me | solution 1 for polynomial_auxiliary_bounds_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:44.080866+00:00
-- url     : https://prove2.me/submissions/6b6d99b9-010b-4cc6-a25c-6bcd22f4ed99

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_polynomialSupNorm_smul
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (p : Polynomial ℂ) (hm : 0 < polynomialSupNorm p K)
    (hnormalized : ∀ q : Polynomial ℂ, polynomialSupNorm q K = 1 →
      ‖Polynomial.aeval A q +
        star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
      ‖Polynomial.aeval A q * crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p K ∧
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p K ^ 2 := by
  let m := polynomialSupNorm p K
  let q : Polynomial ℂ := ((m : ℂ)⁻¹) • p
  have hm' : 0 < m := hm
  have hm0 : m ≠ 0 := ne_of_gt hm'
  have hqnorm : polynomialSupNorm q K = 1 := by
    dsimp only [q]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm']
    exact inv_mul_cancel₀ hm0
  obtain ⟨hsymm, hprod⟩ := hnormalized q hqnorm
  have hp : (m : ℂ) • q = p := by
    dsimp only [q]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm0), one_smul]
  constructor
  · calc
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ =
          m * ‖Polynomial.aeval A q +
            star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ := by
        rw [← hp, norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm']
      _ ≤ m * 2 := mul_le_mul_of_nonneg_left hsymm hm'.le
      _ = 2 * polynomialSupNorm p K := by simp only [m]; ring
  · calc
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ =
          m ^ 2 *
            ‖Polynomial.aeval A q * crouzeixPolynomialAuxiliaryOperator A Omega q‖ := by
        rw [← hp, norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm']
      _ ≤ m ^ 2 * 1 := mul_le_mul_of_nonneg_left hprod (sq_nonneg m)
      _ = polynomialSupNorm p K ^ 2 := by simp only [m, mul_one]
