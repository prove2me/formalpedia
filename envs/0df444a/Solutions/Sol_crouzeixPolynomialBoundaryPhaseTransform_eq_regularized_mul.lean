-- Prove2me | solution 1 for crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:32.355471+00:00
-- url     : https://prove2.me/submissions/05dac452-4f32-4861-9fa5-75efa1d72508

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi q =
      crouzeixPolynomialScalarCompanionRegularized Omega
        ((Polynomial.X - Polynomial.C xi) * q) xi xi := by
  symm
  rw [
    crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform,
    Polynomial.mul_divByMonic_cancel_left q
      (Polynomial.monic_X_sub_C xi)]
