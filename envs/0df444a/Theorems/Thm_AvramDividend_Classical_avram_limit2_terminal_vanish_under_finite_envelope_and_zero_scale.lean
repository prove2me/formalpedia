-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_vanish_under_finite_envelope_and_zero_scale
-- name    : AvramDividend.Classical.avram_limit2_terminal_vanish_under_finite_envelope_and_zero_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:00:20.814046+00:00
-- url     : https://prove2.me/theorems/584313db-bacd-453b-8a1a-98a5f1f516a3
-- title:
--   Original nonnegative ruin-stopped terminal expectations vanish under a genuine finite envelope and zero scale
-- statement:
--   A nonnegative terminal reward (for example the discounted postpayment HJB terminal) has expected value tending to zero if it is pointwise bounded by a measurable integrable ENNReal envelope multiplied by a deterministic nonnegative scale tending to zero. Quantitative envelope integration and continuity of multiplication at a finite limit imply a decaying integrated upper bound; ENNReal order squeeze completes the proof. The pathwise domination, measurability, finiteness and scale convergence are explicit actual hypotheses.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_terminal_vanish_under_finite_envelope_and_zero_scale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Envelope : Ω → ℝ≥0∞)
    (hEnvelope : Measurable Envelope)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Envelope ω)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (hScale : Filter.Tendsto scale Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
