-- Prove2me | solution 1 for measurableSet_isConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:37.75275+00:00
-- url     : https://prove2.me/submissions/6337652c-3fdb-41f6-a2d9-813ad22871c3

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_VersionSpace

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool | IsSampleConsistent (enum n) S} := by
  unfold IsSampleConsistent
  have : {S : Fin m → X × Bool | ∀ i, enum n (S i).1 = (S i).2}
      = ⋂ i, {S | enum n (S i).1 = (S i).2} := by
    ext S; simp [mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun i => measurableSet_eq_fun ?_ (measurable_pi_apply i).snd
  exact (h_meas n).comp (measurable_pi_apply i).fst
