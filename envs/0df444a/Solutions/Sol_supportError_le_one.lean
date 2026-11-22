-- Prove2me | solution 1 for supportError_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:53.524572+00:00
-- url     : https://prove2.me/submissions/fc3800aa-8c17-4bdb-b432-ac37d093ae73

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
    (h c : X → Bool) : supportError Y q h c ≤ 1 := by
  calc supportError Y q h c
      ≤ ∑ y : ↥Y, q.prob y := Finset.sum_le_sum fun y _ =>
        mul_le_of_le_one_right (q.prob_nonneg y) (by split_ifs <;> norm_num)
    _ = 1 := q.prob_sum_one
