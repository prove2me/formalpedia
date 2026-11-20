-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_positive_event_to_integrable_signed_remainder
-- name    : AvramDividend.Classical.avram_pj_workerC_positive_event_to_integrable_signed_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:03:55.599148+00:00
-- url     : https://prove2.me/theorems/9f6b8442-9d50-46ed-88d9-45976e7582b1
-- title:
--   Positive event L1 budget with nonpositive complement gives integrable signed upper envelope and negative remainder
-- statement:
--   From a small positive part integral on S, and G-U nonpositive off S, construct the integrable nonnegative error supported on S and a nonpositive signed remainder such that G-U ≤ E+R. No stochastic assumptions.
-- source:
--   Exact deterministic integrability certificate needed to close Worker C pure-jump positive-clock reward75 route without inventing a compensator.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_positive_event_to_integrable_signed_remainder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S)
    (G U : Ω → ℝ) (ε : ℝ)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hOff : ∀ ω, ω ∉ S → G ω - U ω ≤ 0)
    (hSmall : (∫ ω in S, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε) :
    ∃ E R : Ω → ℝ,
      Integrable E P ∧
      (∫ ω, |E ω| ∂P) ≤ ε ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, G ω - U ω ≤ E ω + R ω) := by sorry
