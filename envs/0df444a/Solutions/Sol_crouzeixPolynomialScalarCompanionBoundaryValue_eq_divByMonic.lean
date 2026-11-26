-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_eq_divByMonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:12.596084+00:00
-- url     : https://prove2.me/submissions/7f37e909-62de-40f5-af93-640904b09b44

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral
            (fun sigma ↦
              star (sigma - xi) *
                star (Polynomial.eval sigma
                  (p /ₘ (Polynomial.X - Polynomial.C xi))) *
                (sigma - xi)⁻¹)
            Omega.boundaryParam := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic]
