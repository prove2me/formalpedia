-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:20.11104+00:00
-- url     : https://prove2.me/submissions/984d88ed-647a-439b-8b52-593a8beaaa8c

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Theorems.Thm_diffContOnCl_crouzeixPolynomialScalarCompanion_extension

set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier)
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖g z‖ ≤ C)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖g z‖ ≤ C := by
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hbounded
    (diffContOnCl_crouzeixPolynomialScalarCompanion_extension
      Omega p g hcont heq) hC hz
