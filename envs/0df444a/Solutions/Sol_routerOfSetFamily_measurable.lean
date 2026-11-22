-- Prove2me | solution 1 for routerOfSetFamily_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:48.799819+00:00
-- url     : https://prove2.me/submissions/adc3382b-bbfd-477e-8443-08380e68bdb4

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    Measurable (fun p : ℕ × X => routerOfSetFamily A p.1 p.2) := by
  simp only [routerOfSetFamily]
  have hS : MeasurableSet {p : ℕ × X | p.2 ∈ A p.1} := by
    have : {p : ℕ × X | p.2 ∈ A p.1} = ⋃ n, {n} ×ˢ A n := by
      ext ⟨n, x⟩
      simp [Set.mem_iUnion, Set.mem_prod]
    rw [this]
    exact MeasurableSet.iUnion (fun n => (measurableSet_singleton n).prod (hA n))
  exact Measurable.piecewise hS measurable_const measurable_const
