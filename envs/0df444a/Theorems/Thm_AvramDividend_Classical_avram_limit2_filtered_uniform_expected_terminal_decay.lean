-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_filtered_uniform_expected_terminal_decay
-- name    : AvramDividend.Classical.avram_limit2_filtered_uniform_expected_terminal_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:24:23.860193+00:00
-- url     : https://prove2.me/theorems/504392d5-e59d-4a08-aa39-2b12d9fd4100
-- title:
--   General cofinal real-horizon terminal vanishing under uniform expectation control
-- statement:
--   For a general filter of horizon indices (including real times tending to infinity), a uniform finite expected undiscounted payoff bound and a vanishing deterministic scale imply that the expected nonnegative terminal payoff vanishes. This is a conditional quantitative reduction and does not assume its original stochastic-process estimate.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_filtered_uniform_expected_terminal_decay
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (l : Filter ι) (scale : ι → ℝ≥0∞)
    (Payoff Terminal : ι → Ω → ℝ≥0∞)
    (hPayoff : ∀ i, Measurable (Payoff i))
    (hBound : ∀ i ω, Terminal i ω ≤ scale i * Payoff i ω)
    (M : ℝ≥0∞) (hUniform : ∀ i, (∫⁻ ω, Payoff i ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤)
    (hScale : Filter.Tendsto scale l (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun i => ∫⁻ ω, Terminal i ω ∂P)
      l (nhds (0 : ℝ≥0∞)) := by sorry
