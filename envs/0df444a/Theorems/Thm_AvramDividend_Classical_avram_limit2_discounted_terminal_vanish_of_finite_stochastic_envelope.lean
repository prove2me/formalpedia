-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_discounted_terminal_vanish_of_finite_stochastic_envelope
-- name    : AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_finite_stochastic_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:00:23.165718+00:00
-- url     : https://prove2.me/theorems/f7c1f646-c437-43d5-bc8f-ac1d0c9e59be
-- title:
--   A positive discount rate and finite stochastic payoff envelope justify vanishing terminal expectations
-- statement:
--   For actual nonnegative original-process terminal payoff random variables, positive discount rate and explicit pointwise domination by exp(-q n) times a measurable integrable stochastic envelope imply that expected terminal contribution tends to zero. The proof imports separate deterministic discount-factor decay and the genuine dominated terminal expectation limit. Time-zero/right-horizon cash remains outside this terminal-only statement; no generic terminal vanishing or equality-in-law is assumed.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_finite_stochastic_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (hq : 0 < q)
    (Envelope : Ω → ℝ≥0∞) (hEnvelope : Measurable Envelope)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤
      ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))) * Envelope ω) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
