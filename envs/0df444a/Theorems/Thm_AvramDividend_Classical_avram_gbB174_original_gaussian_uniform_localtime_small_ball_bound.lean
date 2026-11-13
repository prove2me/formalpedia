-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB174_original_gaussian_uniform_localtime_small_ball_bound
-- name    : AvramDividend.Classical.avram_gbB174_original_gaussian_uniform_localtime_small_ball_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:35:54.04868+00:00
-- url     : https://prove2.me/theorems/525072de-0a3a-4304-8ed1-dc2314527440
-- title:
--   Original controlled Gaussian reserve uniform small-ball local-time estimate
-- statement:
--   Original controlled Gaussian reserve satisfies a uniform small-ball occupation estimate at every centre and all radii up to one, using locally bounded Gaussian semimartingale local time. B171, B172 and B173 give finite variation and nondegenerate volatility inputs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB174_original_gaussian_uniform_localtime_small_ball_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ (y ε : ℝ),
      0 < ε → ε ≤ 1 →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - y) < ε} ≤
        ENNReal.ofReal ((L : ℝ) * ε) := by sorry
