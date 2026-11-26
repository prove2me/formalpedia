-- Prove2me | solution 1 for periodic_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:18.684046+00:00
-- url     : https://prove2.me/submissions/24a5cbf6-d8ad-421f-9e9b-c7d177266d8c

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_periodic_polytopeSoftSupport


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    (u : Finset ℂ) (delta rho : ℝ) :
    Function.Periodic (polytopeRoundedSupport u delta rho)
      (2 * Real.pi) := by
  intro theta
  unfold polytopeRoundedSupport
  rw [periodic_polytopeSoftSupport u delta theta]
