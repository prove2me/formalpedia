-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:58.223121+00:00
-- url     : https://prove2.me/submissions/c4296b76-86d5-492a-8fff-1949dc233ab1

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary

set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier)
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖g z‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  rw [← heq hz]
  exact norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
    Omega p g hbounded hcont heq hC (subset_closure hz)
