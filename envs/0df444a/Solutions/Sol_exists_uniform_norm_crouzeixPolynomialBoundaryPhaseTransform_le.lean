-- Prove2me | solution 1 for exists_uniform_norm_crouzeixPolynomialBoundaryPhaseTransform_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:34.806787+00:00
-- url     : https://prove2.me/submissions/ec1bf26a-355b-4ca5-afec-79d0341e7925

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_norm_crouzeixPolynomialBoundaryPhaseTransform_le
import Theorems.Thm_exists_nonneg_bound_boundaryParam_deriv


set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (xi : ℂ) (q : Polynomial ℂ),
      ‖crouzeixPolynomialBoundaryPhaseTransform Omega xi q‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm q (frontier Omega.carrier))) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun xi q ↦
    norm_crouzeixPolynomialBoundaryPhaseTransform_le
      Omega xi q hD_nonneg hD⟩
