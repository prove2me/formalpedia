-- Prove2me | solution 1 for ordinalVCDim_inner_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:05.682589+00:00
-- url     : https://prove2.me/submissions/88202d2e-934f-4587-8481-316e8f1dc0cc

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) (C : ConceptClass X Bool)
    (S : Finset X) :
    BddAbove (Set.range (fun (_ : Shatters X C S) => ((S.card : ℕ) : Ordinal))) :=
  ⟨S.card, fun _ ⟨_, h⟩ => h ▸ le_refl _⟩
