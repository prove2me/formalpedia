-- Prove2me | solution 1 for policy_gradient_discounted_finite
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-10T05:07:45.986658+00:00
-- url     : https://prove2.me/submissions/df9654eb-f75d-4fbb-8159-9aef6215fda3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_policy_gradient_finite_horizon
import Theorems.Thm_pg_rho_gamma_scale
import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open Finset

/-- Discounted finite-horizon PGT: specialize `policy_gradient_finite_horizon` to
`P ← γ·P` and use `pg_rho_gamma_scale`. -/
theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (γ : ℝ) (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ) (T : ℕ) (s₀ : S), deriv (fun θ' => pgValue (fun s a s' => γ * P s a s') r π T θ' s₀) θ = ∑ t ∈ Finset.range T, γ ^ t * ∑ s : S, pgRho P π t s₀ θ s * ∑ a : A, pgQ (fun s a s' => γ * P s a s') r π (T - 1 - t) θ s a * deriv (fun θ' => π θ' s a) θ := by
  intro S A _ _ _ P r π θ γ hdiff T s₀
  rw [policy_gradient_finite_horizon (fun s a s' => γ * P s a s') r π θ hdiff T s₀]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [pg_rho_gamma_scale P π θ γ t s₀ s]
  ring
