-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:44.145061+00:00
-- url     : https://prove2.me/submissions/d94ea9b9-5308-46ae-9768-c5b66d3d2fff

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension

set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z)))
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖b z‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
    Omega p (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      hbounded
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
        Omega p b hlim)
      (fun w hw ↦ crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hw)
      (fun w hw ↦ ?_) hz
  rw [crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
    Omega p b hlim hw]
  exact hC w hw
