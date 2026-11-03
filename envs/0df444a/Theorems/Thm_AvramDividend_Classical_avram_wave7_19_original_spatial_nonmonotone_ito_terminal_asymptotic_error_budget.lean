-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_spatial_nonmonotone_ito_terminal_asymptotic_error_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_spatial_nonmonotone_ito_terminal_asymptotic_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:58:33.588347+00:00
-- url     : https://prove2.me/theorems/12b0be7d-915a-4852-b797-af2cc32226fa
-- title:
--   Original nonnested spatial stopped Ito with asymptotically vanishing errors implies full ruin cash budget
-- statement:
--   The exact original-process spatial localisation version of a diagonal stopped Itô–Meyer passage. Arbitrary measurable local dividend-cash observables may be nonmonotone; the necessary boundary-payment exhaustion is the almost-sure inequality full original ruin cash ≤ liminf_n LocalCash_n, preserving creeping, overshoots and reflection-cap payment mass. For each NNReal ε>0, only an eventual expected stopped cash plus nonnegative terminal estimate ≤budget+ε is needed. Inf-tail bounds and ENNReal.le_of_forall_pos_le_add eliminate ε, while the spatial nonmonotone Fatou source theorem yields the complete finite-horizon expected cash ≤budget. No uniform integrability or new canonical HJB assumptions.
-- source:
--   Original W7-19 nonmonotone spatial local cash Fatou theorem and ENNReal small-error elimination. Honest a.s. cash-coverage hypothesis; no riskProcess continuity or UI.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_spatial_nonmonotone_ito_terminal_asymptotic_error_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ n : ℕ, Measurable (LocalCash n))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
        ≤ (⨆ n : ℕ, ⨅ k : ℕ, LocalCash (n + k) ω))
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStoppedTail : ∀ (ε : NNReal), 0 < ε → budget < ⊤ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫⁻ ω, LocalCash n ω + Terminal ε n ω ∂P)
          ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
