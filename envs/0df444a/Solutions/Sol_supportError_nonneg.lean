-- Prove2me | solution 1 for supportError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:51.82275+00:00
-- url     : https://prove2.me/submissions/a9d91c55-3341-4d4f-8868-2f656ed76b3e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) : 0 ≤ supportError Y q h c :=
  Finset.sum_nonneg fun y _ =>
    mul_nonneg (q.prob_nonneg y) (by split_ifs <;> norm_num)
