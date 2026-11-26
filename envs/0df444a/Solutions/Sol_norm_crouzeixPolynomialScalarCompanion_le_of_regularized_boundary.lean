-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:44.442518+00:00
-- url     : https://prove2.me/submissions/a002dd1d-8245-4b37-a63e-4673d786d160

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_regularized
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
    Omega p (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
      hbounded
      (fun xi hxi ↦ tendsto_crouzeixPolynomialScalarCompanion_of_regularized
        Omega p hkernel xi (hreg xi hxi))
      hC hz
