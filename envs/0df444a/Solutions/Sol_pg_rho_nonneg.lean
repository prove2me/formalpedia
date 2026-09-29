-- Prove2me | solution 1 for pg_rho_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T04:26:38.9416+00:00
-- url     : https://prove2.me/submissions/40cc22d0-5bfb-49b7-af75-14e8fd4a0ed1

import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

open Finset

theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (hP : ∀ s a s', 0 ≤ P s a s') (hπ : ∀ s a, 0 ≤ π θ s a), ∀ (t : ℕ) (s₀ s : S), 0 ≤ pgRho P π t s₀ θ s := by
  intro S A _ _ _ P π θ hP hπ t
  induction t with
  | zero =>
    intro s₀ s
    rw [show pgRho P π 0 s₀ θ s = if s = s₀ then 1 else 0 from rfl]
    split <;> norm_num
  | succ m ih =>
    intro s₀ s
    rw [show pgRho P π (m + 1) s₀ θ s
        = ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π m s' θ s from rfl]
    apply Finset.sum_nonneg
    intro s' _
    apply mul_nonneg
    · apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (hπ s₀ a) (hP s₀ a s')
    · exact ih s' s
