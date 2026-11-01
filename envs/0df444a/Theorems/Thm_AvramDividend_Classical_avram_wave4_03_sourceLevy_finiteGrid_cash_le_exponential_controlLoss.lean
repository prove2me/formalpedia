-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_cash_le_exponential_controlLoss
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_cash_le_exponential_controlLoss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:43:54.218727+00:00
-- url     : https://prove2.me/theorems/7b30d5fd-2e0c-4f8d-8371-adc70052d46f
-- title:
--   Original Lévy finite-grid dividend cash dominated by exponential postpayment control loss
-- statement:
--   The exact finite-grid θ-weighted entire right-limit Stieltjes dividend cash of the same original Lévy source is pointwise bounded by the sum of its postpayment exponential control losses. This is an all-path scalar convexity inequality with no atom-only restriction, and supplies an L1 envelope once source Lévy product integrability is known.
-- source:
--   Canonical scalar exponential control loss 17... and right-limit dividend monotonicity; applies to original X same path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_cash_le_exponential_controlLoss
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (ω : Ω) :
    θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ≤
    ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) := by sorry
