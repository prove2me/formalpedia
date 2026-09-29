-- Prove2me | solution 1 for likelihood_ratio_gradient
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T03:46:15.375095+00:00
-- url     : https://prove2.me/submissions/b61abada-d0c9-4671-82e2-d885adfc5795

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset

/-- Likelihood-ratio / REINFORCE gradient identity. Differentiate the finite sum
term by term, then use `deriv log (p θ' a) = p'(a)/p(θ,a)` and cancel `p(θ,a)`. -/
theorem solution {A : Type} [Fintype A]
    (p : ℝ → A → ℝ) (f : A → ℝ) (θ : ℝ)
    (hdiff : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ)
    (hpos : ∀ a, 0 < p θ a) :
    deriv (fun θ' => ∑ a : A, p θ' a * f a) θ
      = ∑ a : A, p θ a * f a * deriv (fun θ' => Real.log (p θ' a)) θ := by
  -- Turn `fun θ' => ∑ a, g a θ'` into `∑ a, g a` (pointwise function sum) for `deriv_sum`.
  have hfn_eq : (fun θ' => ∑ a : A, p θ' a * f a)
      = ∑ a : A, (fun θ' => p θ' a * f a) := by
    ext x
    exact (Finset.sum_apply x (Finset.univ : Finset A) (fun a θ' => p θ' a * f a)).symm
  -- Each summand is differentiable.
  have hdiff_term : ∀ a ∈ (Finset.univ : Finset A),
      DifferentiableAt ℝ (fun θ' => p θ' a * f a) θ :=
    fun a _ => (hdiff a).mul_const (f a)
  rw [hfn_eq, deriv_sum hdiff_term]
  apply Finset.sum_congr rfl
  intro a _
  -- Goal: deriv (fun θ' => p θ' a * f a) θ = p θ a * f a * deriv (fun θ' => log (p θ' a)) θ
  have hne : p θ a ≠ 0 := ne_of_gt (hpos a)
  have hlog : deriv (fun θ' => Real.log (p θ' a)) θ
      = deriv (fun θ' => p θ' a) θ / p θ a :=
    ((hdiff a).hasDerivAt.log hne).deriv
  rw [hlog, deriv_mul_const (hdiff a) (f a)]
  field_simp
