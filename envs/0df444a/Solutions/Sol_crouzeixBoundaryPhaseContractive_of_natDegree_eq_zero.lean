-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:31.866243+00:00
-- url     : https://prove2.me/submissions/03b51aa6-e076-4f8c-84e7-b7fe0ae1f6c5

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Theorems.Thm_norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero


set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hp : p.natDegree = 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  intro xi _hxi
  exact
    norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
      Omega p hp xi
