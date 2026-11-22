-- Prove2me | solution 1 for versionSpaceLearner_measurableBatchLearner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:24.716178+00:00
-- url     : https://prove2.me/submissions/53b8f97c-a4c4-4b0e-ba7e-b1eac64c77c7

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_VersionSpace
public import Theorems.Thm_measurableSet_versionSpace_true

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n)) :
    MeasurableBatchLearner X (versionSpaceLearner enum) := by
  constructor
  intro m
  apply measurable_to_countable'
  intro b
  rcases b with _ | _
  · -- b = false: complement of the true preimage
    have : (fun p : (Fin m → X × Bool) × X =>
        (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {false}
        = ((fun p : (Fin m → X × Bool) × X =>
          (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true})ᶜ := by
      ext ⟨S, x⟩
      simp_all
    rw [this]
    exact (measurableSet_versionSpace_true enum h_meas m).compl
  · -- b = true: countable union of measurable rectangles
    exact measurableSet_versionSpace_true enum h_meas m
