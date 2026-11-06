-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_lintegral_vanish_of_scaled_envelope
-- name    : AvramDividend.Classical.avram_limit2_terminal_lintegral_vanish_of_scaled_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:00:15.653412+00:00
-- url     : https://prove2.me/theorems/e80cec32-301a-4414-aa73-a7a4b48572e8
-- title:
--   Vanishing original stopped terminal expectations from a decaying integrated envelope
-- statement:
--   The expected nonnegative original ruin-stopped terminal payoff tends to zero when it is pointwise dominated by a measurable nonnegative random envelope times a deterministic scalar and the integrated scalar envelope tends to zero. This theorem retains the actual ENNReal terminal quantity and invokes the separate quantitative envelope bound; it never supposes nonnegativity alone causes terminal vanishing.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_terminal_lintegral_vanish_of_scaled_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (scale : ℕ → ℝ≥0∞)
    (Envelope : Ω → ℝ≥0∞)
    (hEnvelope : Measurable Envelope)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Envelope ω)
    (hDecay : Filter.Tendsto
      (fun n : ℕ => scale n * (∫⁻ ω, Envelope ω ∂P))
      Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
