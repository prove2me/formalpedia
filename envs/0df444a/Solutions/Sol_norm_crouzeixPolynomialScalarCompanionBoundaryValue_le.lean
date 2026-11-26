-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:38.144833+00:00
-- url     : https://prove2.me/submissions/8b201188-d3e7-44bf-8879-03feaea878c0

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm


set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) +
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  calc
    ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
        ‖star (Polynomial.eval xi p)‖ +
          ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ :=
      norm_add_le _ _
    _ ≤ polynomialSupNorm p (frontier Omega.carrier) +
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by
      apply add_le_add
      · rw [norm_star]
        exact norm_eval_le_polynomialSupNorm p
          (bddAbove_norm_eval_image_of_isCompact p Omega.isCompact_frontier)
          hxi
      · exact norm_crouzeixPolynomialScalarCompanionRegularized_self_le
          Omega p xi hD_nonneg hD
