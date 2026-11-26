-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanionRegularized_self_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:07.9928+00:00
-- url     : https://prove2.me/submissions/59af3c68-5d1d-4281-91ce-e23f82a16e20

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_contourIntegral_le_of_norm_le_const
import Theorems.Thm_norm_eval_boundaryParam_le_polynomialSupNorm_frontier
import Theorems.Thm_polynomialSupNorm_nonneg
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (D * polynomialSupNorm
            (p /ₘ (Polynomial.X - Polynomial.C xi))
            (frontier Omega.carrier))) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C xi)
  have heval : ∀ sigma : ℂ,
      Polynomial.eval sigma p - Polynomial.eval xi p =
        (sigma - xi) * Polynomial.eval sigma q := by
    intro sigma
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        ((star (Polynomial.eval (Omega.boundaryParam t) p) -
            star (Polynomial.eval xi p)) *
          (Omega.boundaryParam t - xi)⁻¹)‖ ≤
        D * polynomialSupNorm q (frontier Omega.carrier) := by
    intro t ht
    by_cases hzero : Omega.boundaryParam t = xi
    · simp only [hzero, sub_self, inv_zero, mul_zero, smul_zero, norm_zero]
      exact mul_nonneg hD_nonneg (polynomialSupNorm_nonneg q _)
    · have hdiff : Omega.boundaryParam t - xi ≠ 0 :=
        sub_ne_zero.mpr hzero
      have hdiffNorm : ‖Omega.boundaryParam t - xi‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hdiff
      have hstar :
          star (Polynomial.eval (Omega.boundaryParam t) p) -
              star (Polynomial.eval xi p) =
            star (Omega.boundaryParam t - xi) *
              star (Polynomial.eval (Omega.boundaryParam t) q) := by
        rw [← star_sub, heval, star_mul]
        ring
      rw [hstar]
      simp only [smul_eq_mul, norm_mul, norm_star, norm_inv]
      calc
        ‖deriv Omega.boundaryParam t‖ *
              ((‖Omega.boundaryParam t - xi‖ *
                  ‖Polynomial.eval (Omega.boundaryParam t) q‖) *
                ‖Omega.boundaryParam t - xi‖⁻¹) =
            ‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t) q‖ := by
          calc
            _ = ‖deriv Omega.boundaryParam t‖ *
                (‖Polynomial.eval (Omega.boundaryParam t) q‖ *
                  (‖Omega.boundaryParam t - xi‖ *
                    ‖Omega.boundaryParam t - xi‖⁻¹)) := by ring
            _ = _ := by rw [mul_inv_cancel₀ hdiffNorm, mul_one]
        _ ≤ D * polynomialSupNorm q (frontier Omega.carrier) :=
          mul_le_mul (hD t ht)
            (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega q t)
            (norm_nonneg _) hD_nonneg
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)
