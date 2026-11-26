-- Prove2me | solution 1 for hasDerivAt_crouzeixPolynomialScalarCompanion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:34.948595+00:00
-- url     : https://prove2.me/submissions/eec162c8-39fe-4c2f-9d23-cdf3f3ba33af

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    HasDerivAt (crouzeixPolynomialScalarCompanion Omega p)
      (crouzeixPolynomialScalarCompanionDeriv Omega p z) z := by
  apply hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
  intro hfrontier
  have hempty : z ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hz, hfrontier⟩
  exact hempty
