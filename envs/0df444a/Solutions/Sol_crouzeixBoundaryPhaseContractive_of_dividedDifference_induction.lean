-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:55.230577+00:00
-- url     : https://prove2.me/submissions/02836e28-bddf-44ac-987f-a74832633bbb

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Theorems.Thm_polynomial_induction_on_boundaryPhaseDividedDifferences
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hstep : ∀ p, 0 < p.natDegree →
      (∀ xi ∈ frontier Omega.carrier,
        CrouzeixBoundaryPhaseContractive Omega
          (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      CrouzeixBoundaryPhaseContractive Omega p) :
    ∀ p, CrouzeixBoundaryPhaseContractive Omega p := by
  apply polynomial_induction_on_boundaryPhaseDividedDifferences Omega
  · exact crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero Omega
  · exact hstep
