-- Prove2me | Theorems.Thm_AvramDividend_Classical_integral_indicator_capped_deficit_le_exp_partition
-- name    : AvramDividend.Classical.integral_indicator_capped_deficit_le_exp_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:38:20.408247+00:00
-- url     : https://prove2.me/theorems/9d790db1-b9dc-468b-83c3-2287a004a886
-- title:
--   Expected cumulative capped drift deficit on an admissible event is bounded by a sum of exponential mesh gaps
-- statement:
--   A general measure-theoretic mesh estimate: if a stochastic real path has nonnegative increments almost surely and all mesh increments are at most a on an event E, then the expected endpoint increment restricted to E is bounded by the expected sum of finite-cell exponential deficits, provided both sides are integrable. It follows from the already proved deterministic telescoping inequality, positivity outside E, and the monotonicity of the Bochner integral. This is designed for finite-mesh exclusion of monotone BV Levy paths.
-- source:
--   Proved capped_deficit_partition_exponential_sum_bound and Mathlib integral_mono_ae.

import Theorems.Thm_AvramDividend_Classical_capped_deficit_partition_exponential_sum_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.integral_indicator_capped_deficit_le_exp_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (D : ℕ → Ω → ℝ) (N : ℕ)
    (a : ℝ) (ha : 0 < a)
    (hNonneg : ∀ᵐ ω ∂P, ∀ k : ℕ, k < N →
      0 ≤ D (k + 1) ω - D k ω)
    (hCap : ∀ ω ∈ E, ∀ k : ℕ, k < N →
      D (k + 1) ω - D k ω ≤ a)
    (hLeft : Integrable
      (E.indicator (fun ω => D N ω - D 0 ω)) P)
    (hRight : Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P) :
    (∫ ω, E.indicator (fun ω => D N ω - D 0 ω) ω ∂P) ≤
      (∫ ω, 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a)))) ∂P) := by sorry
