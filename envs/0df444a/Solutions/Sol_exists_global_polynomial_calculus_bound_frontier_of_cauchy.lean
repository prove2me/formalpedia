-- Prove2me | solution 1 for exists_global_polynomial_calculus_bound_frontier_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:19.889378+00:00
-- url     : https://prove2.me/submissions/5eecaf99-cee9-4244-8854-b14fa379ebe2

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_norm_eval_boundaryParam_le_polynomialSupNorm_frontier
import Theorems.Thm_exists_bound_crouzeixPolynomialAuxiliaryIntegrand
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_contourIntegral_le_of_norm_le_const
import Theorems.Thm_polynomialSupNorm_nonneg
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : ∀ p : Polynomial ℂ, Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z ↦ Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (frontier Omega.carrier) := by
  obtain ⟨C, hC⟩ :=
    exists_bound_crouzeixPolynomialAuxiliaryIntegrand A Omega (Polynomial.C 1) hOmega
  have hkernel : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        resolvent A (Omega.boundaryParam t)‖ ≤ C := by
    intro t ht
    simpa only [Polynomial.eval_C, star_one, one_smul] using hC t ht
  have hC0 : 0 ≤ C :=
    (norm_nonneg (deriv Omega.boundaryParam 0 •
      resolvent A (Omega.boundaryParam 0))).trans
      (hkernel 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let K : ℝ := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)
  refine ⟨K, mul_nonneg (norm_nonneg _) (mul_nonneg Real.two_pi_pos.le hC0), ?_⟩
  intro p
  have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (Polynomial.eval (Omega.boundaryParam t) p •
          resolvent A (Omega.boundaryParam t))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) * C := by
    intro t ht
    rw [smul_smul, norm_smul, norm_mul]
    calc
      ‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval (Omega.boundaryParam t) p‖ *
            ‖resolvent A (Omega.boundaryParam t)‖ =
          ‖Polynomial.eval (Omega.boundaryParam t) p‖ *
            ‖deriv Omega.boundaryParam t •
              resolvent A (Omega.boundaryParam t)‖ := by
        rw [norm_smul]
        ring
      _ ≤ polynomialSupNorm p (frontier Omega.carrier) * C :=
        mul_le_mul (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t)
          (hkernel t ht) (norm_nonneg _) (polynomialSupNorm_nonneg p _)
  rw [hCauchy p, norm_smul]
  calc
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        ‖contourIntegral (fun z ↦ Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi * (polynomialSupNorm p (frontier Omega.carrier) * C)) :=
      mul_le_mul_of_nonneg_left
        (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)
    _ = K * polynomialSupNorm p (frontier Omega.carrier) := by
      simp only [K]
      ring
