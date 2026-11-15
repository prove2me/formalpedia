-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_integrable_norm_series_ae_summability
-- name    : AvramDividend.Classical.avram_b24_integrable_norm_series_ae_summability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:32:50.317937+00:00
-- url     : https://prove2.me/theorems/6033494b-05b5-4956-a224-bb382ce35e43
-- title:
--   Summable integrals of norms imply almost-sure absolute summability and an integrable dominating envelope
-- statement:
--   Tonelli and finite-integral transfer for a series of integrable real-valued measurable functions. A summable sequence of L1 norms yields almost-sure absolute summability and an integrable envelope bounding every individual term. This is the reusable norm-series compactness ingredient for B24 gain increment convergence.
-- source:
--   Tonelli nonnegative-series theorem and Bochner integral norm summability, pinned Mathlib.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_integrable_norm_series_ae_summability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (H : ℕ → Ω → ℝ)
    (hHI : ∀ k, Integrable (H k) P)
    (hSum : Summable (fun k => ∫ ω, ‖H k ω‖ ∂P)) :
    ∃ (B : Ω → ℝ),
      Integrable B P ∧
      (∀ᵐ ω ∂P, Summable (fun k => ‖H k ω‖)) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖H k ω‖ ≤ B ω) := by sorry
