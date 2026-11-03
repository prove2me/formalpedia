-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_diagonal_ito_terminal_asymptotic_error_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_overshooting_diagonal_ito_terminal_asymptotic_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:46:14.347998+00:00
-- url     : https://prove2.me/theorems/bbb0638c-b140-45c4-82e6-67b8b7e4d52d
-- title:
--   Original diagonal stopped Ito with eventually small jump error and nonnegative terminal implies full ruin cash
-- statement:
--   For possibly nonmonotone W7-18 clocks whose a.s. tail lower limit covers ruin, the actual W7-05/06/07 diagonal jump-truncation estimates need only hold eventually in the clock index for each ε>0, with nonnegative ENNReal terminal terms. For every ε and finite budget choose N so the stopped Ito cash+terminal expectation is ≤budget+ε for all n≥N. Dropping the terminal, each tail-infimum of stopped expected cash is ≤budget+ε by inspecting the future index m+N. Taking the supremum of tail infima, then ENNReal.le_of_forall_pos_le_add, gives liminf of stopped expectations ≤budget. The exact W7-19 diagonal Fatou expectation bridge yields the full pre-ruin discounted dividendMeasure cash bound. No UI, no uniform-in-n-for-all-ε hypothesis, no source continuity at ruin, and all original canonical assumptions remain untouched.
-- source:
--   W7-19 diagonal source Fatou expected cash 7d8962b1-c1e2-4eff-a485-9548fbeee31a once Proved; ENNReal.le_of_forall_pos_le_add and tail-inf order bound. Actual stopping clock/cofinality and Ito residual remain explicit source obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_overshooting_diagonal_ito_terminal_asymptotic_error_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminfLower : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStoppedTail : ∀ (ε : NNReal), 0 < ε → budget < ⊤ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
          Terminal ε n ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
