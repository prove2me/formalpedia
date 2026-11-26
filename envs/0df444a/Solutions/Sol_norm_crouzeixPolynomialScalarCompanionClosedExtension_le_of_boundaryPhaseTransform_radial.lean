-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:15.378189+00:00
-- url     : https://prove2.me/submissions/8229cc5b-7df7-4998-9778-98dd125769b8

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  have hbounded :=
    Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  apply
    norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
      Omega p hbounded hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hphase
  · exact hz
