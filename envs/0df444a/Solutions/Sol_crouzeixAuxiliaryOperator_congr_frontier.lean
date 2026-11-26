-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_congr_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:02:30.848778+00:00
-- url     : https://prove2.me/submissions/2119fecc-26cf-4f77-8fbc-8ff667cfd259

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_congr_boundaryParam

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : Set.EqOn f g (frontier Omega.carrier)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by
  apply crouzeixAuxiliaryOperator_congr_boundaryParam
  intro t _ht
  apply hfg
  rw [← Omega.boundaryParam_range]
  exact mem_range_self t
