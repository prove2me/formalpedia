-- Prove2me | solution 1 for pg_value_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T03:48:43.016391+00:00
-- url     : https://prove2.me/submissions/d6e0596b-5758-4d78-baec-b6b8356be13b

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset

namespace PGHelper

/-- `DifferentiableAt` through a `Finset.sum` written in `fun`-form. -/
lemma diffAt_fun_sum {ι : Type} {s : Finset ι} {f : ι → ℝ → ℝ} {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) θ) :
    DifferentiableAt ℝ (fun x => ∑ i ∈ s, f i x) θ := by
  have heq : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    ext x; exact (Finset.sum_apply x s f).symm
  rw [heq]; exact DifferentiableAt.sum h

end PGHelper

open PGHelper

/-- `pgValue` is differentiable in `θ`, by induction on the horizon. -/
theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ), ∀ (k : ℕ) (s : S), DifferentiableAt ℝ (fun θ' => pgValue P r π k θ' s) θ := by
  intro S A _ _ P r π θ hdiff k
  induction k with
  | zero =>
    intro s
    -- pgValue 0 θ' s = 0
    have : (fun θ' => pgValue P r π 0 θ' s) = (fun _ => (0 : ℝ)) := by
      ext x; rfl
    rw [this]; exact differentiableAt_const 0
  | succ m ih =>
    intro s
    -- pgValue (m+1) θ' s = ∑ a, π θ' s a * (r s a + ∑ s', P s a s' * pgValue m θ' s')
    have hunfold : (fun θ' => pgValue P r π (m+1) θ' s)
        = (fun θ' => ∑ a : A, π θ' s a * (r s a + ∑ s' : S, P s a s' * pgValue P r π m θ' s')) := by
      ext x; rfl
    rw [hunfold]
    apply diffAt_fun_sum
    intro a _
    apply DifferentiableAt.mul (hdiff s a)
    -- (fun θ' => r s a + ∑ s', P s a s' * pgValue m θ' s') differentiable
    apply DifferentiableAt.const_add
    apply diffAt_fun_sum
    intro s' _
    exact DifferentiableAt.const_mul (ih s') (P s a s')
