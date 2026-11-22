-- Prove2me | solution 1 for formalLearning_analyticSet_nullMeasurableSet_ghostPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:20.095948+00:00
-- url     : https://prove2.me/submissions/1f68b472-982c-4d40-aea1-2bbc79fec7a3

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Theorems.Thm_formalLearning_analyticSet_nullMeasurableSet


set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {m : ℕ} {s : Set ((Fin m → X) × (Fin m → X))}
    (hs : MeasureTheory.AnalyticSet s)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    MeasureTheory.NullMeasurableSet s (GhostPairMeasure D m) := by
  have : MeasureTheory.IsFiniteMeasure (GhostPairMeasure D m) := inferInstance
  exact formalLearning_analyticSet_nullMeasurableSet hs
