-- Prove2me | solution 1 for exists_inward_boundary_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:06.888701+00:00
-- url     : https://prove2.me/submissions/7cb75a10-5f92-4ab3-a9be-b33ef6146037

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_exists_uniform_inward_boundary_denominator_bound

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
        r * delta ≤ ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_uniform_inward_boundary_denominator_bound Omega hc
  refine ⟨delta, hdelta, ?_⟩
  intro r hr sigma hsigma
  exact hbound xi hxi r hr sigma hsigma
