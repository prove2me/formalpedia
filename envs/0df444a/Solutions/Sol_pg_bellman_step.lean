-- Prove2me | solution 1 for pg_bellman_step
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-10T04:00:20.554551+00:00
-- url     : https://prove2.me/submissions/ceb0060e-b478-4735-88f0-c38d377c011e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_pg_value_differentiable
import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset

/-- Bellman gradient step: differentiate `V_{k+1}(s) = ∑_a π(a|s) · (r(s,a) + ∑_{s'} P·V_k)` by
the product rule, using that `r` and `P` are `θ`-independent. Needs `pg_value_differentiable`
so that `deriv` of the inner value functions is well-defined. -/
theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ) (k : ℕ) (s : S), deriv (fun θ' => pgValue P r π (k+1) θ' s) θ = (∑ a : A, pgQ P r π k θ s a * deriv (fun θ' => π θ' s a) θ) + ∑ a : A, π θ s a * ∑ s' : S, P s a s' * deriv (fun θ' => pgValue P r π k θ' s') θ := by
  intro S A _ _ P r π θ hdiff k s
  -- V_k differentiable for all (k, s).
  have hVdiff := pg_value_differentiable P r π θ hdiff
  -- Unfold V_{k+1}.
  have hunfold : (fun θ' => pgValue P r π (k+1) θ' s)
      = (fun θ' => ∑ a : A, π θ' s a * (r s a + ∑ s' : S, P s a s' * pgValue P r π k θ' s')) := by
    ext x; rfl
  -- Inner "g a": r s a + ∑_{s'} P·V_k.
  have hg_diff : ∀ a, DifferentiableAt ℝ
      (fun θ' => r s a + ∑ s' : S, P s a s' * pgValue P r π k θ' s') θ := by
    intro a
    exact (DifferentiableAt.fun_sum fun s' _ =>
      DifferentiableAt.const_mul (hVdiff k s') (P s a s')).const_add (r s a)
  have hg_deriv : ∀ a, deriv
      (fun θ' => r s a + ∑ s' : S, P s a s' * pgValue P r π k θ' s') θ
      = ∑ s' : S, P s a s' * deriv (fun θ' => pgValue P r π k θ' s') θ := by
    intro a
    rw [deriv_const_add, deriv_fun_sum (fun s' _ =>
      DifferentiableAt.const_mul (hVdiff k s') (P s a s'))]
    exact Finset.sum_congr rfl fun s' _ => deriv_const_mul (P s a s') (hVdiff k s')
  -- Differentiate V_{k+1} = ∑_a π(s,a) · g a.
  rw [hunfold, deriv_fun_sum (fun a _ => DifferentiableAt.fun_mul (hdiff s a) (hg_diff a))]
  -- For each `a`: deriv(π·g) = deriv π · g + π · deriv g, then reorganize.
  have hterm : ∀ a ∈ (Finset.univ : Finset A),
      deriv (fun θ' => π θ' s a * (r s a + ∑ s' : S, P s a s' * pgValue P r π k θ' s')) θ
      = pgQ P r π k θ s a * deriv (fun θ' => π θ' s a) θ
        + π θ s a * ∑ s' : S, P s a s' * deriv (fun θ' => pgValue P r π k θ' s') θ := by
    intro a _
    rw [deriv_fun_mul (hdiff s a) (hg_diff a), hg_deriv a]
    have hQ : r s a + ∑ s' : S, P s a s' * pgValue P r π k θ s' = pgQ P r π k θ s a := rfl
    rw [hQ]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
