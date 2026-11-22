-- Prove2me | solution 1 for finite_approx_minimax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:15.681665+00:00
-- url     : https://prove2.me/submissions/9ac9418e-0dfe-465e-8058-147c8fdfcb1f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Theorems.Thm_boolGamePayoff_nonneg
public import Theorems.Thm_covering_minimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C] [Nonempty R]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (hε_feasible : v - ε ≤ 1 / Fintype.card C) :
    ∃ p : FinitePMF R, ∀ c : C,
      v - ε ≤ boolGamePayoff M p c := by
  classical
  by_cases hv : v ≤ 0
  · exact ⟨uniformPMF R, fun c => le_trans (by linarith) (boolGamePayoff_nonneg M _ c)⟩
  · push Not at hv
    obtain ⟨p, hp⟩ := covering_minimax M v hv hrow
    exact ⟨p, fun c => le_trans hε_feasible (hp c)⟩
