-- Prove2me | solution 1 for nat_find_eq_iff_isFirstConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:39.722792+00:00
-- url     : https://prove2.me/submissions/b9a5ec96-ce55-4f77-ad68-3d7babb00afd

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
    {X : Type u} (enum : ℕ → Concept X Bool)
    {m : ℕ} (S : Fin m → X × Bool)
    (h : ∃ n, IsSampleConsistent (enum n) S) (n : ℕ) :
    Nat.find h = n ↔ IsFirstConsistent enum S n := by
  simp only [IsFirstConsistent, Nat.find_eq_iff]
