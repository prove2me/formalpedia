-- Prove2me | solution 1 for ordinalVCDim_outer_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:06.190732+00:00
-- url     : https://prove2.me/submissions/65a8573e-037a-43f8-9aa0-54e1c907761c

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
theorem _root_.solution (X : Type u) (C : ConceptClass X Bool) :
    BddAbove (Set.range (fun S : Finset X =>
      ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal))) := by
  refine ⟨Ordinal.omega0, fun x ⟨S, hS⟩ => ?_⟩
  subst hS
  apply ciSup_le'
  intro _
  exact le_of_lt (Ordinal.natCast_lt_omega0 S.card)
