-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_congr_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:13.63946+00:00
-- url     : https://prove2.me/submissions/1bb367ec-f15f-46da-a0fc-a5b7f20747b5

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_congr_frontier

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : Set.EqOn f g (closure Omega.carrier)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by
  apply crouzeixAuxiliaryOperator_congr_frontier
  exact hfg.mono frontier_subset_closure
