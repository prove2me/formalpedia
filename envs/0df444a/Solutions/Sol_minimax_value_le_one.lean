-- Prove2me | solution 1 for minimax_value_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:16.611487+00:00
-- url     : https://prove2.me/submissions/1fbf782f-4ea0-4496-8e2e-6f50bcbfa4e2

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    v ≤ 1 := by
  obtain ⟨r, hr⟩ := hrow (uniformPMF C)
  calc v ≤ ∑ c : C, (uniformPMF C).prob c *
      (if M r c then (1 : ℝ) else 0) := hr
    _ ≤ ∑ c : C, (uniformPMF C).prob c := Finset.sum_le_sum fun c _ =>
        mul_le_of_le_one_right ((uniformPMF C).prob_nonneg c)
          (by split_ifs <;> norm_num)
    _ = 1 := (uniformPMF C).prob_sum_one
