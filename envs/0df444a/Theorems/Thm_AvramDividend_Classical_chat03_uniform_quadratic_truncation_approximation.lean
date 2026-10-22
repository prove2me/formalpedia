-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_uniform_quadratic_truncation_approximation
-- name    : AvramDividend.Classical.chat03_uniform_quadratic_truncation_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:24:46.679733+00:00
-- url     : https://prove2.me/theorems/d923897e-9527-47e8-b38a-46dfe72ec03f
-- title:
--   Uniform quadratic control of clipped expectations
-- statement:
--   For an almost-everywhere nonnegative measurable sequence and a target variable, when both sequence and target have integrable squares bounded by the same C, a single positive clipping threshold makes every sequence expectation and the target expectation close to their corresponding truncated expectations within any prescribed tolerance.
-- source:
--   Accepted quadratic real truncation error estimate and explicit positive-threshold choice.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_error_bound
import Theorems.Thm_AvramDividend_Classical_chat03_positive_cutoff_makes_quadratic_error_small

open MeasureTheory Filter Topology AvramDividend.Classical

theorem AvramDividend.Classical.chat03_uniform_quadratic_truncation_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hZm : AEStronglyMeasurable Z P)
    (hZ0 : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C)
    (hZ2 : Integrable (fun ω => (Z ω) ^ 2) P ∧
      ∫ ω, (Z ω) ^ 2 ∂P ≤ C) :
    ∀ ε > 0, ∃ R > 0,
      (∀ n, dist (∫ ω, Y n ω ∂P)
        (∫ ω, min (Y n ω) R ∂P) ≤ ε) ∧
      dist (∫ ω, min (Z ω) R ∂P) (∫ ω, Z ω ∂P) ≤ ε := by sorry
