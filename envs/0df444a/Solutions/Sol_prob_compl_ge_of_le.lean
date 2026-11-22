-- Prove2me | solution 1 for prob_compl_ge_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:27.852566+00:00
-- url     : https://prove2.me/submissions/adf793d2-6421-442a-a12a-186ca4319791

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
theorem _root_.solution {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hbound : μ s ≤ ENNReal.ofReal δ) :
    μ sᶜ ≥ ENNReal.ofReal (1 - δ) := by
  rw [MeasureTheory.measure_compl hs (ne_top_of_le_ne_top ENNReal.one_ne_top
    (MeasureTheory.prob_le_one)), MeasureTheory.IsProbabilityMeasure.measure_univ]
  calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
    _ ≤ 1 - μ s := tsub_le_tsub_left hbound 1
