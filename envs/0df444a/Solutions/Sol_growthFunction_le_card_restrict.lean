-- Prove2me | solution 1 for growthFunction_le_card_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:06.21962+00:00
-- url     : https://prove2.me/submissions/b48928d1-1e40-46d3-9fb5-b00c46175f00

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u}
    (C : Finset (X → Bool)) (S : Finset X) :
    (restrictConceptClass C S).card ≤ C.card :=
  Finset.card_image_le
