-- Prove2me | solution 1 for target_in_versionSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:12.710752+00:00
-- url     : https://prove2.me/submissions/c26e346d-dd1e-4f09-aa39-90aa2fabdfe9

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X : Type} {C : ConceptClass X Bool}
    {c : X → Bool} (hcC : c ∈ C) {history : List (X × Bool)}
    (hcons : ∀ p ∈ history, c p.1 = p.2) :
    c ∈ versionSpace C history :=
  ⟨hcC, hcons⟩
