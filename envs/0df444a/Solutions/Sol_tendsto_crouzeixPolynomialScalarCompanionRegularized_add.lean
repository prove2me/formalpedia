-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:44.422646+00:00
-- url     : https://prove2.me/submissions/d37623d5-9b81-4510-a32d-f1a0940b35b6

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_self
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ)
    (hp : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hq : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega q xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega q xi xi))) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized
        Omega (p + q) xi xi)) := by
  rw [crouzeixPolynomialScalarCompanionRegularized_add_self]
  apply (hp.add hq).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier]
  intro hfrontier
  have hempty : z ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hz, hfrontier⟩
  exact hempty
