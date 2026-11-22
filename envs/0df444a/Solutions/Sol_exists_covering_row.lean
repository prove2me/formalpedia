-- Prove2me | solution 1 for exists_covering_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:19.429539+00:00
-- url     : https://prove2.me/submissions/7a203114-df61-4b7a-8f3a-60307c152f40

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ c₀ : C, ∃ r : R, M r c₀ = true := by
  classical
  intro c₀
  obtain ⟨r, hr⟩ := hrow (pointMassPMF c₀)
  refine ⟨r, ?_⟩
  by_contra h
  have hf : M r c₀ = false := Bool.eq_false_iff.mpr h
  have : (∑ c : C, (pointMassPMF c₀).prob c *
      (if M r c then (1 : ℝ) else 0)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro c _
    simp only [pointMassPMF]
    split_ifs with h1 h2
    · subst h1; rw [hf] at h2; exact absurd h2 Bool.false_ne_true
    all_goals simp
  linarith
