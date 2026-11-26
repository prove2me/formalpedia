-- Prove2me | solution 1 for norm_crouzeixPolynomialBoundaryPhaseTransform_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:33.46012+00:00
-- url     : https://prove2.me/submissions/942686d5-d04b-4b13-a92c-f96e2cb6b68a

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionRegularized_self_le

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialBoundaryPhaseTransform Omega xi q‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (D * polynomialSupNorm q (frontier Omega.carrier))) := by
  rw [crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul]
  have h := norm_crouzeixPolynomialScalarCompanionRegularized_self_le
    Omega ((Polynomial.X - Polynomial.C xi) * q) xi hD_nonneg hD
  have hquot :
      (Polynomial.X - Polynomial.C xi) * q /ₘ
          (Polynomial.X - Polynomial.C xi) = q :=
    Polynomial.mul_divByMonic_cancel_left q
      (Polynomial.monic_X_sub_C xi)
  rw [hquot] at h
  exact h
