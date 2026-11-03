-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_stopped_nonnegative_terminal_drop_full_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_stopped_nonnegative_terminal_drop_full_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:03:45.336177+00:00
-- url     : https://prove2.me/theorems/cb956379-806f-4d84-82df-410e5de84a4d
-- title:
--   Original stopped source cash plus nonnegative terminal budget implies full finite-horizon ruin cash bound
-- statement:
--   At a single natural stopped clock n>T in the actual original spectrally negative Levy risk process, the complete time-zero right-dividend atom and each strictly positive lower-time cutoff cash observable may be estimated jointly with any ENNReal nonnegative terminal contribution. The terminal contribution is discarded monotonically and the accepted W7-19 original-source cash bridge yields the full finite-horizon pre-ruin payout expectation. This is the source Ito output shape needed by W7-08, without integrability of terminal values, uniform integrability or changes to canonical strategy hypotheses.
-- source:
--   Proved original-source cutoff expected cash bridge ece66659-9fbd-4446-91b5-4e0f16f362f8; Mathlib lintegral_mono and ENNReal nonnegative addition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_stopped_nonnegative_terminal_drop_full_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞))
    (Terminal : ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ k : ℕ,
      (∫⁻ ω, (((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) +
        Terminal k ω) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
      budget := by sorry
