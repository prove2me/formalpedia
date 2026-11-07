-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_original_physical_generator_drift_sum_nonpos
-- name    : AvramDividend.Classical.avram_a19_original_physical_generator_drift_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:36:54.504323+00:00
-- url     : https://prove2.me/theorems/52591942-0b0c-455e-8690-359308d0b38c
-- title:
--   Original stopped physical-grid HJB generator contribution is pathwise nonpositive
-- statement:
--   For any monotone stopped physical time grid, the original Lévy-process HJB generator contribution is nonpositive on every sample path. Each active cell has a positive discount factor, nonpositive generator-minus-discount value, and nonnegative time increment; inactive cells contribute zero. The theorem preserves the exact original risk-process left limits, ruin stopping and cap-interior tests.
-- source:
--   Pathwise sign of the explicit first summand in B_n from the original physical stopped-cell source 2bc848f9. The result is independent of the hard compensated-jump martingale and Stieltjes-error estimates, and directly follows from the original HJB inequality and grid monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_original_physical_generator_drift_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by sorry
