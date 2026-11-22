-- Prove2me | solution 1 for versionSpace_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:00.85895+00:00
-- url     : https://prove2.me/submissions/a9715eaa-a098-46a6-a724-ed6e619fd915

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    versionSpace C history ⊆ C :=
  fun _ hm => hm.1
