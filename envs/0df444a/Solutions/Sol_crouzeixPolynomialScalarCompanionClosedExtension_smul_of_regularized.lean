-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:20.683806+00:00
-- url     : https://prove2.me/submissions/cb5bd5ba-4482-4a4a-826f-f9f68fc20ecd

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanion_smul


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hp : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by
  have hscaled : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi)
        (nhdsWithin xi Omega.carrier)
        (nhds (crouzeixPolynomialScalarCompanionRegularized
          Omega (a • p) xi xi)) := by
    intro xi hxi
    exact tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
      Omega a p xi (hp xi hxi)
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Omega (a • p) hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hz,
      crouzeixPolynomialScalarCompanion_smul]
  · rw [
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega (a • p) hkernel hscaled hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega p hkernel hp hz,
      crouzeixPolynomialScalarCompanionBoundaryValue_smul]
