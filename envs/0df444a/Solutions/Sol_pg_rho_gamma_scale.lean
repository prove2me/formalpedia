-- Prove2me | solution 1 for pg_rho_gamma_scale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T05:06:15.361103+00:00
-- url     : https://prove2.me/submissions/f7da07fe-0e33-47b3-852f-b4d62bb45f42

import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open Finset

/-- Discounting the transition kernel scales `pgRho` by `γ^t`. -/
theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (γ : ℝ), ∀ (t : ℕ) (s₀ s : S), pgRho (fun s a s' => γ * P s a s') π t s₀ θ s = γ ^ t * pgRho P π t s₀ θ s := by
  intro S A _ _ _ P π θ γ t
  induction t with
  | zero =>
    intro s₀ s
    rw [show pgRho (fun s a s' => γ * P s a s') π 0 s₀ θ s = if s = s₀ then (1:ℝ) else 0 from rfl,
        show pgRho P π 0 s₀ θ s = if s = s₀ then (1:ℝ) else 0 from rfl, pow_zero, one_mul]
  | succ m ih =>
    intro s₀ s
    calc pgRho (fun s a s' => γ * P s a s') π (m + 1) s₀ θ s
        = ∑ s' : S, (∑ a : A, π θ s₀ a * (γ * P s₀ a s'))
            * pgRho (fun s a s' => γ * P s a s') π m s' θ s := rfl
      _ = ∑ s' : S, (γ * ∑ a : A, π θ s₀ a * P s₀ a s')
            * (γ ^ m * pgRho P π m s' θ s) := by
          apply Finset.sum_congr rfl; intro s' _
          congr 1
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
          · exact ih s' s
      _ = γ ^ (m + 1) * ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π m s' θ s := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro s' _; ring
      _ = γ ^ (m + 1) * pgRho P π (m + 1) s₀ θ s := by
          congr 1
