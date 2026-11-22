-- Prove2me | solution 1 for pac_sample_complexity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:34.162278+00:00
-- url     : https://prove2.me/submissions/13f4169c-de44-45ea-9274-2badce645ce5

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (d : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 < d) :
    0 < PACsampleComplexity d ε δ := by
  unfold PACsampleComplexity
  apply Nat.lt_ceil.mpr
  simp only [Nat.cast_zero]
  apply mul_pos (div_pos (by norm_num : (0:ℝ) < 8) hε)
  apply add_pos
  · exact mul_pos (Nat.cast_pos.mpr hd) (Real.log_pos ((one_lt_div hε).mpr (by linarith)))
  · exact Real.log_pos ((one_lt_div hδ).mpr (by linarith))
