-- Prove2me | solution 1 for withTopNatToOrdinal_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:31.00774+00:00
-- url     : https://prove2.me/submissions/be0d27ed-521b-4e7b-b1ff-aac7d2f80abd

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
theorem _root_.solution :
    ∀ a b : WithTop ℕ, a ≤ b → withTopNatToOrdinal a ≤ withTopNatToOrdinal b := by
  intro a b hab
  match a, b with
  | some n, some m =>
    exact Nat.cast_le.mpr (WithTop.coe_le_coe.mp hab)
  | some n, none =>
    exact le_of_lt (Ordinal.natCast_lt_omega0 n)
  | none, none =>
    exact le_refl _
  | none, some m =>
    exact absurd hab (WithTop.not_top_le_coe m)
