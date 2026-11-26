-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:41:31.131058+00:00
-- url     : https://prove2.me/submissions/bcb429c4-554d-41c4-98b7-8d1b6107b921

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_regularized
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
      Omega p (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
  · intro z hz
    exact tendsto_crouzeixPolynomialScalarCompanion_of_regularized
      Omega p hkernel z (hreg z hz)
  · exact hxi
