-- Prove2me | solution 1 for periodic_polytopeSoftPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:19.550301+00:00
-- url     : https://prove2.me/submissions/75dabf14-efa0-4dc6-ac09-b54bd19549bb

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Theorems.Thm_periodic_polytopeDirectionalValue

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (u : Finset ℂ) (delta : ℝ) :
    Function.Periodic (polytopeSoftPartition u delta) (2 * Real.pi) := by
  intro theta
  unfold polytopeSoftPartition
  apply Finset.sum_congr rfl
  intro z hz
  rw [periodic_polytopeDirectionalValue z theta]
