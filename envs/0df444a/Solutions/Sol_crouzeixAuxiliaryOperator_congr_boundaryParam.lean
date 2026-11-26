-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_congr_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:30.570812+00:00
-- url     : https://prove2.me/submissions/e34c870b-c1eb-405e-aa66-35e2a1d5204e

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      f (Omega.boundaryParam t) = g (Omega.boundaryParam t)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by
  unfold crouzeixAuxiliaryOperator
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le Real.two_pi_pos.le] at ht
  change deriv Omega.boundaryParam t •
      (f (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t)) =
    deriv Omega.boundaryParam t •
      (g (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t))
  rw [hfg t ht]
