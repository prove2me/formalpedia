-- Prove2me | solution 1 for convexThickeningApprox_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:54.416248+00:00
-- url     : https://prove2.me/submissions/73e18c98-651e-4f01-8815-4623a4e591e2

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution (K : Set ℂ) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) :
    (∀ n, K ⊆ convexThickeningApprox K n ∧
      IsOpen (convexThickeningApprox K n) ∧
      StrictConvex ℝ (convexThickeningApprox K n)) ∧
      (⋂ n, convexThickeningApprox K n) = K := by
  constructor
  · intro n
    refine ⟨Metric.self_subset_thickening (smoothApproxRadius_pos n) K,
      Metric.isOpen_thickening, ?_⟩
    exact (hconvex.thickening (smoothApproxRadius n)).strictConvex_of_isOpen
      Metric.isOpen_thickening
  · exact iInter_convexThickeningApprox K hcompact.isClosed
