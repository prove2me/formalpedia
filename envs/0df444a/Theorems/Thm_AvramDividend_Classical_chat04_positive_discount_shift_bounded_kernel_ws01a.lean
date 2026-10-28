-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_shift_bounded_kernel_ws01a
-- name    : AvramDividend.Classical.chat04_positive_discount_shift_bounded_kernel_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:21:59.514047+00:00
-- url     : https://prove2.me/theorems/0da982e0-25bb-4bc7-a2aa-7e99da45faec
-- title:
--   Construct subunit causal renewal kernel for q-to-(q+p) scale discount shift
-- statement:
--   Given any unbounded-variation q-scale function with q>0 and p>0, construct a positive bounded continuous causal kernel K(x)=p exp(-θx)W^(q)(x) whose Laplace mass p/(ψ(θ)-q) lies strictly between zero and one. The kernel is the independently justified Neumann-series starting point for constructing a (q+p)-scale function directly from the scale witness supplied by the primary theorem.
-- source:
--   Accepted generic weighted scale bound b9952447 and exponent growth f06e514c; IsScaleFunction's own q-scale Laplace transform; zero-origin and continuity results. No exit identity or killed semigroup harmonicity.

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_discount_shift_bounded_kernel_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (Wq : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq) (p : ℝ) (hp : 0 < p) :
    ∃ θ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 ≤ θ ∧ q + p < X.ψ θ ∧ 0 < ρ ∧ ρ < 1 ∧
      Continuous K ∧ BddAbove (Set.range (fun x : ℝ => ‖K x‖)) ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ ∧
      (∀ x : ℝ, x ≤ 0 → K x = 0) ∧
      (∀ x : ℝ, 0 ≤ K x) ∧
      (∀ x : ℝ, K x = p * (Real.exp (-(θ * x)) * Wq x)) := by sorry
