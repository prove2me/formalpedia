-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_weak_limit_of_tight_approximants
-- name    : AvramDividend.Classical.excursion_laplace_weak_limit_of_tight_approximants
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:20:47.062332+00:00
-- url     : https://prove2.me/theorems/32aa3f05-934c-4e90-9bea-a1e3c8f52c8b
-- title:
--   Extract a finite positive measure with specified Laplace transform from tight approximating resolvents
-- statement:
--   If finite positive approximating measures β_n have constant mass 1/k, support on [0,∞), are uniformly tight, and their Laplace transforms converge pointwise to 1/F(s), then Prokhorov compactness gives a weakly convergent subsequence. The limit μ retains mass and nonnegative support, and bounded continuous exponential test functions identify its Laplace transform with 1/F(s). This is the exact weak-limit step of the infinite-activity killed Bernstein resolvent.
-- source:
--   Pinned Mathlib Prokhorov, FiniteMeasure.tendsto_iff_forall_integral_tendsto, Portmanteau.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_laplace_weak_limit_of_tight_approximants
    (β : ℕ → Measure ℝ) (k : ℝ) (hk : 0 < k)
    (F : ℝ → ℝ)
    (hFpos : ∀ s : ℝ, 0 ≤ s → 0 < F s)
    (hmass : ∀ n : ℕ, β n univ = ENNReal.ofReal (k⁻¹))
    (hsupport : ∀ n : ℕ, β n (Iio (0 : ℝ)) = 0)
    (htight : IsTightMeasureSet (Set.range β))
    (hconv : ∀ s : ℝ, 0 ≤ s →
      Tendsto
        (fun n : ℕ =>
          ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂β n)
        atTop (𝓝 (ENNReal.ofReal ((F s)⁻¹)))) :
    ∃ μ : Measure ℝ,
      μ (Iio (0 : ℝ)) = 0 ∧
      μ univ = ENNReal.ofReal (k⁻¹) ∧
      (∀ s : ℝ, 0 ≤ s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) =
          ENNReal.ofReal ((F s)⁻¹)) := by sorry
