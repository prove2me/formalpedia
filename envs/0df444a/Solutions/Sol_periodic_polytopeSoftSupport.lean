-- Prove2me | solution 1 for periodic_polytopeSoftSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:55.599041+00:00
-- url     : https://prove2.me/submissions/bc5c067c-7c0e-4e89-88a6-512464c95fae

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Theorems.Thm_periodic_polytopeSoftPartition

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (u : Finset ℂ) (delta : ℝ) :
    Function.Periodic (polytopeSoftSupport u delta) (2 * Real.pi) := by
  intro theta
  unfold polytopeSoftSupport
  rw [periodic_polytopeSoftPartition u delta theta]
