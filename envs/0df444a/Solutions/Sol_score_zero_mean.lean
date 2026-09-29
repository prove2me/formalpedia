-- Prove2me | solution 1 for score_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T04:41:45.389204+00:00
-- url     : https://prove2.me/submissions/53c8453d-0343-4ed2-b1b3-e492baeca78f

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

open Finset

/-- The score function has zero mean: `∑_a p_θ(a) ∇log p_θ(a) = 0`. -/
theorem solution : ∀ {A : Type} [Fintype A] (p : ℝ → A → ℝ) (θ : ℝ) (hdiff : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ) (hpos : ∀ a, 0 < p θ a) (hnorm : ∀ θ', ∑ a : A, p θ' a = 1), ∑ a : A, p θ a * deriv (fun θ' => Real.log (p θ' a)) θ = 0 := by
  intro A _ p θ hdiff hpos hnorm
  -- `p θ a · deriv(log p(·,a)) θ = p'(a)` pointwise.
  have hcancel : ∀ a ∈ (Finset.univ : Finset A),
      p θ a * deriv (fun θ' => Real.log (p θ' a)) θ = deriv (fun θ' => p θ' a) θ := by
    intro a _
    have hne : p θ a ≠ 0 := ne_of_gt (hpos a)
    rw [((hdiff a).hasDerivAt.log hne).deriv]
    field_simp
  rw [Finset.sum_congr rfl hcancel]
  -- `∑_a p'(a) = deriv (∑_a p(·,a)) θ = deriv 1 θ = 0`.
  have hconv : (∑ a : A, deriv (fun θ' => p θ' a) θ)
      = deriv (fun θ' => ∑ a : A, p θ' a) θ := (deriv_fun_sum (fun a _ => hdiff a)).symm
  rw [hconv]
  have hconst : (fun θ' => ∑ a : A, p θ' a) = (fun _ => (1:ℝ)) := by
    ext θ'; exact hnorm θ'
  rw [hconst, deriv_const]
