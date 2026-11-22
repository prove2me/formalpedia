-- Prove2me | solution 1 for mwu_potential_T_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:32.198727+00:00
-- url     : https://prove2.me/submissions/d9c6e02b-0a61-4d86-9a39-635bccde2c58

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Theorems.Thm_minimax_value_le_one
public import Theorems.Thm_mwuInit_potential
public import Theorems.Thm_potential_one_step_bound

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) :
    (mwuConfig M η hη1 v hrow T).potential ≤
    Fintype.card C * (1 - η * v) ^ T := by
  induction T with
  | zero =>
    simp only [mwuConfig, mwuRun, mwuInit_potential, pow_zero, mul_one, le_refl]
  | succ T ih =>
    simp only [mwuConfig, mwuRun] at ih ⊢
    set run_T := mwuRun M η hη1 v hrow T
    set cfg_T := run_T.1
    set r := (hrow cfg_T.toPMF).choose
    have hstep := potential_one_step_bound M η hη hη1 v hrow cfg_T
    simp only [cfg_T] at hstep
    have hv1 : v ≤ 1 := minimax_value_le_one M v hrow
    have h1ηv : 0 ≤ 1 - η * v := by nlinarith [mul_le_of_le_one_left hη hv1]
    calc (mwuUpdateWeights M η hη1 cfg_T
            ((hrow cfg_T.toPMF).choose)).potential
        ≤ cfg_T.potential * (1 - η * v) := hstep
      _ ≤ (↑(Fintype.card C) * (1 - η * v) ^ T) * (1 - η * v) :=
          mul_le_mul_of_nonneg_right ih h1ηv
      _ = ↑(Fintype.card C) * (1 - η * v) ^ (T + 1) := by ring
