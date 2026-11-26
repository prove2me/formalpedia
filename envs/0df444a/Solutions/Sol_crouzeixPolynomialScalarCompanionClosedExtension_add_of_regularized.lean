-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:00.200886+00:00
-- url     : https://prove2.me/submissions/a1054d6a-7047-404f-8aa2-0f98609ace7d

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_add
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_add
import Theorems.Thm_crouzeixPolynomialScalarCompanion_add
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq

section
open Complex Filter MeasureTheory Set
open scoped Interval Real
private theorem not_mem_frontier_of_mem_carrier
    (Omega : SmoothJordanDomain) {z : ℂ} (hz : z ∈ Omega.carrier) :
    z ∉ frontier Omega.carrier := by
  intro hfrontier
  have hempty : z ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hz, hfrontier⟩
  exact hempty
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hp : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hq : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega q xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega q xi xi)))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by
  have hsum : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi)
        (nhdsWithin xi Omega.carrier)
        (nhds (crouzeixPolynomialScalarCompanionRegularized
          Omega (p + q) xi xi)) := by
    intro xi hxi
    exact tendsto_crouzeixPolynomialScalarCompanionRegularized_add
      Omega p q xi (hp xi hxi) (hq xi hxi)
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Omega (p + q) hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq Omega q hz,
      crouzeixPolynomialScalarCompanion_add Omega p q
        (not_mem_frontier_of_mem_carrier Omega hz)]
  · rw [
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega (p + q) hkernel hsum hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega p hkernel hp hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega q hkernel hq hz,
      crouzeixPolynomialScalarCompanionBoundaryValue_add]
