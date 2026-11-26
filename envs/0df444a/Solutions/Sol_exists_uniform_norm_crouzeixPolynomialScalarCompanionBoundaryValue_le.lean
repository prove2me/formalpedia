-- Prove2me | solution 1 for exists_uniform_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:35.458531+00:00
-- url     : https://prove2.me/submissions/09a75742-22b0-4994-b064-3977da953a84

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
import Theorems.Thm_exists_nonneg_bound_boundaryParam_deriv


set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (xi : ℂ),
      xi ∈ frontier Omega.carrier →
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (2 * Real.pi *
              (D * polynomialSupNorm
                (p /ₘ (Polynomial.X - Polynomial.C xi))
                (frontier Omega.carrier))) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun p xi hxi ↦
    norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
      Omega p hxi hD_nonneg hD⟩
