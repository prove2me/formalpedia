-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_HJB_cell_sum_nonpos
-- name    : AvramDividend.Classical.avram_p3_grid4_original_physical_HJB_cell_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:21:34.693322+00:00
-- url     : https://prove2.me/theorems/822d8e24-41c9-4ff3-8e56-a9bf163850cb
-- title:
--   Nonpositive original BV HJB generator-cell sum on the strict stopped physical mesh
-- statement:
--   For the genuine original spectrally negative Levy X and dividend strategy D, the discounted HJB generator contribution over every time-increasing finite physical grid row is nonpositive. The summand is precisely the first masked generator part of B_n in 2bc848f9; outside the strict positive sub-cap pre-ruin state it is zero. The only sign assumptions are the original interior HJB inequality and nonnegative cell durations; no artificial smoothness at zero, cap, ruin or a stochastic mean-zero assertion is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_physical_HJB_cell_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
    (∑ i ∈ Finset.range (n + 1),
      if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u (i + 1) : ℝ) - (u i : ℝ))
      else 0) ≤ 0 := by sorry
