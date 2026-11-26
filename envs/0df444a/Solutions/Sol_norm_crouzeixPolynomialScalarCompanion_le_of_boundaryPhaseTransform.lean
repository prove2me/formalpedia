-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:49.042021+00:00
-- url     : https://prove2.me/submissions/30e24c47-af1e-4766-baf8-dd187a9234a9

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary


set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Filter.Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
    Omega p hbounded hkernel hreg
  · intro xi hxi
    rw [
      crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
    exact hphase xi hxi
  · exact hz
