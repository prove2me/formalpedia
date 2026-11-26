-- Prove2me | solution 1 for exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:09.388566+00:00
-- url     : https://prove2.me/submissions/85e40c89-3e85-40bd-b180-c1bd4403650c

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Theorems.Thm_exists_nonneg_bound_boundaryParam_deriv
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm

set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (z : ℂ),
      z ∉ frontier Omega.carrier →
      ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            ((D * polynomialSupNorm p (frontier Omega.carrier)) *
              (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun p z hz ↦
    norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
      Omega p hD_nonneg hD hz⟩
