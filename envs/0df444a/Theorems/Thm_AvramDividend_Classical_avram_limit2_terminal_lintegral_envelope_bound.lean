-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_lintegral_envelope_bound
-- name    : AvramDividend.Classical.avram_limit2_terminal_lintegral_envelope_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:00:12.097198+00:00
-- url     : https://prove2.me/theorems/07ceb8ef-8137-4d0e-aee8-1a67cd2a98c4
-- title:
--   Dominated original stopped terminal envelope gives a quantitative integrated budget
-- statement:
--   For a measurable nonnegative stochastic envelope and arbitrary nonnegative terminal payments bounded pointwise by a deterministic ENNReal scale times that envelope, every expected terminal payment is bounded by the same scale times the envelope's expected value. No assertion of vanishing is made without an actual scale limit and finite envelope integral.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_terminal_lintegral_envelope_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (scale : ℕ → ℝ≥0∞)
    (Envelope : Ω → ℝ≥0∞)
    (hEnvelope : Measurable Envelope)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Envelope ω) :
    ∀ n, (∫⁻ ω, Terminal n ω ∂P) ≤
      scale n * (∫⁻ ω, Envelope ω ∂P) := by sorry
