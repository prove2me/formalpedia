-- Prove2me | solution 1 for measurableSet_isFirstConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:16.242979+00:00
-- url     : https://prove2.me/submissions/c6992026-a46e-4fe1-b940-91d086cd1008

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_VersionSpace
public import Theorems.Thm_measurableSet_isConsistent

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
    MeasurableSet {S : Fin m → X × Bool | IsFirstConsistent enum S n} := by
  unfold IsFirstConsistent
  have : {S : Fin m → X × Bool |
      IsSampleConsistent (enum n) S ∧ ∀ k, k < n → ¬IsSampleConsistent (enum k) S}
      = {S | IsSampleConsistent (enum n) S} ∩
        (⋂ k, ⋂ (_ : k < n), {S | IsSampleConsistent (enum k) S}ᶜ) := by
    ext S; simp [mem_inter_iff, mem_iInter, mem_compl_iff]
  rw [this]
  refine (measurableSet_isConsistent enum h_meas m n).inter ?_
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    (measurableSet_isConsistent enum h_meas m k).compl
