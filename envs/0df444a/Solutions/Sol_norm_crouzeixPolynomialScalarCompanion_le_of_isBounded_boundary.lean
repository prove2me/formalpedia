-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:44.559234+00:00
-- url     : https://prove2.me/submissions/6b517f58-cacb-4a1c-825c-33838aae7826

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
    Omega p hbounded hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hC
  · exact hz
