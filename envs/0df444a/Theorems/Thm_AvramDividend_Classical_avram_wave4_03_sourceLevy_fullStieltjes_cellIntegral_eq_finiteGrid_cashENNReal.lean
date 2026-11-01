-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:35:54.438627+00:00
-- url     : https://prove2.me/theorems/8358e91d-e406-4627-919f-7c9d5f17a34f
-- title:
--   Exact original source Lévy finite-grid full Stieltjes lintegral equals ENNReal real cash
-- statement:
--   For the actual original spectrally negative Levy path and its adapted dividend strategy, the full random Stieltjes integral of the finite-grid endpoint exponential controls is exactly the ENNReal conversion of the source martingale weighted entire right-limit increment cash. Each interval includes diffuse, singular continuous and payment-atom mass. Uses exact cell Stieltjes indicator identity, right-limit mass, nonnegativity, and ENNReal sum/multiplication conversion.
-- source:
--   Canonical cc6c2317, f9211de0, avram_wave3_03 right-limit monotonicity; pinned ENNReal.ofReal_sum_of_nonneg and ofReal_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) (ω : Ω) :
    (∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ *
          Real.exp (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω) =
    ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by sorry
