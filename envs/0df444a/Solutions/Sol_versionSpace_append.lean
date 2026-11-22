-- Prove2me | solution 1 for versionSpace_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:13.129809+00:00
-- url     : https://prove2.me/submissions/716ca7e7-6eec-444c-87b5-c5e593f20626

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} {x : X} {y : Bool} :
    versionSpace C (history ++ [(x, y)]) ⊆ versionSpace C history := by
  intro c ⟨hcC, hcons⟩
  exact ⟨hcC, fun p hp => hcons p (List.mem_append.mpr (Or.inl hp))⟩
