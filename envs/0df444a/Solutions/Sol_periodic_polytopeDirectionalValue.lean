-- Prove2me | solution 1 for periodic_polytopeDirectionalValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:28.648983+00:00
-- url     : https://prove2.me/submissions/a91af231-2acf-449d-9d3a-0d92cdce83d9

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (z : ℂ) :
    Function.Periodic (polytopeDirectionalValue z) (2 * Real.pi) := by
  intro theta
  unfold polytopeDirectionalValue
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
