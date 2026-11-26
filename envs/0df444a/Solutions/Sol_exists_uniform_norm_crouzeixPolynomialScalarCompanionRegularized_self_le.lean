-- Prove2me | solution 1 for exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:26.851605+00:00
-- url     : https://prove2.me/submissions/86df970a-d55f-46c1-9bd0-6176757ef3f4

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
import Theorems.Thm_exists_nonneg_bound_boundaryParam_deriv


set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (xi : ℂ),
      ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun p xi ↦
    norm_crouzeixPolynomialScalarCompanionRegularized_self_le
      Omega p xi hD_nonneg hD⟩
