-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanion_of_regularized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:52.9968+00:00
-- url     : https://prove2.me/submissions/b8a08a86-0ba1-427d-8773-0768a6f9c77b

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add
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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (xi : ℂ)
    (hreg : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  have hlim : Tendsto
      (fun z ↦ star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi z)
      (nhdsWithin xi Omega.carrier)
      (nhds (star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) :=
    tendsto_const_nhds.add hreg
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi
    (not_mem_frontier_of_mem_carrier Omega hz), hkernel z hz, mul_one]
  exact add_comm _ _
