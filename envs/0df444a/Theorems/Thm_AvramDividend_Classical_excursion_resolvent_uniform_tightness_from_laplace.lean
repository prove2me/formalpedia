-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_resolvent_uniform_tightness_from_laplace
-- name    : AvramDividend.Classical.excursion_resolvent_uniform_tightness_from_laplace
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:19:44.844054+00:00
-- url     : https://prove2.me/theorems/f2895e24-7b69-4e5b-b1db-3c4d849e721e
-- title:
--   Uniform Laplace lower bounds give tight finite resolvent measures
-- statement:
--   Finite measures of common mass 1/k supported on nonnegative reals are uniformly tight if their Laplace transforms are uniformly at least 1/F(s), where F(0)=k>0 and F is continuous at zero. The proof bounds tails using 1−exp(−sR), then chooses s small and R large.
-- source:
--   Pinned Mathlib Prokhorov and IsTightMeasureSet; Laplace tail bound.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_resolvent_uniform_tightness_from_laplace (β : ℕ → Measure ℝ) (k : ℝ) (hk : 0 < k) (F : ℝ → ℝ) (hF0 : F 0 = k) (hFcont : ContinuousAt F 0) (hFpos : ∀ s : ℝ, 0 ≤ s → 0 < F s) (hmass : ∀ n : ℕ, β n univ = ENNReal.ofReal (k⁻¹)) (hsupport : ∀ n : ℕ, β n (Iio (0 : ℝ)) = 0) (hlower : ∀ n : ℕ, ∀ s : ℝ, 0 < s → ENNReal.ofReal ((F s)⁻¹) ≤ (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂β n)) : IsTightMeasureSet (Set.range β) := by sorry
