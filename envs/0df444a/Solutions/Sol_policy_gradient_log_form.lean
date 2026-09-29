-- Prove2me | solution 1 for policy_gradient_log_form
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-10T04:34:29.852595+00:00
-- url     : https://prove2.me/submissions/daa15a8c-a874-44a8-af89-e9e7d7a906b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_policy_gradient_finite_horizon
import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset

/-- Log-derivative form of the finite-horizon policy gradient theorem.
Obtain from `policy_gradient_finite_horizon` by rewriting
`π θ s a · Q · (log π)' = Q · π'` pointwise, using `π θ s a > 0`. -/
theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ) (hpos : ∀ s a, 0 < π θ s a) (T : ℕ) (s₀ : S), deriv (fun θ' => pgValue P r π T θ' s₀) θ = ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s₀ θ s * ∑ a : A, π θ s a * pgQ P r π (T - 1 - t) θ s a * deriv (fun θ' => Real.log (π θ' s a)) θ := by
  intro S A _ _ _ P r π θ hdiff hpos T s₀
  rw [policy_gradient_finite_horizon P r π θ hdiff T s₀]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro s _
  congr 1
  apply Finset.sum_congr rfl; intro a _
  -- Goal: pgQ ... * deriv π = π · pgQ ... · deriv (log π).
  have hne : π θ s a ≠ 0 := ne_of_gt (hpos s a)
  have hlog : deriv (fun θ' => Real.log (π θ' s a)) θ
      = deriv (fun θ' => π θ' s a) θ / π θ s a :=
    ((hdiff s a).hasDerivAt.log hne).deriv
  rw [hlog]
  field_simp
