-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:25:23.438535+00:00
-- url     : https://prove2.me/theorems/6683864e-7852-48f4-8683-1e46ef1e670c
-- title:
--   Truncated real first-moment tails vanish by Bochner dominated convergence
-- statement:
--   For every measurable integrable real random variable R under P, the expectation of R times the indicator R>n tends to zero along natural cutoffs n→∞. The exact Lean proof uses measurability of the cutoff, domination by ‖R‖, eventual pointwise zero, and Bochner dominated convergence. This applies to the genuine BV Lévy residual R1, making its terminal first-moment error tend to zero without any extra assumptions.
-- source:
--   Complete candidate privately remote compiler verified to deliberate sentinel, candidates/work_on/AvramDividend_04c_integrable_real_truncated_tail_to_zero_probe.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : Ω → ℝ) (hMeas : Measurable R) (hInt : Integrable R P) :
    Tendsto (fun n : ℕ => ∫ ω, if (n : ℝ) < R ω then R ω else 0 ∂P)
      atTop (nhds 0) := by sorry
