-- Prove2me | solution 1 for cosh_le_exp_sq_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:54.304857+00:00
-- url     : https://prove2.me/submissions/6a76515e-30dc-4337-97e1-97ed38621f2b

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) :=
  Real.cosh_le_exp_half_sq x
