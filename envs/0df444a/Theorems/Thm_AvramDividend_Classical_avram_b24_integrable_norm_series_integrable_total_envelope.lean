-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_integrable_norm_series_integrable_total_envelope
-- name    : AvramDividend.Classical.avram_b24_integrable_norm_series_integrable_total_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:33:24.829215+00:00
-- url     : https://prove2.me/theorems/28fc3091-0d2a-4942-8619-0d741a6a9151
-- title:
--   L1-summable norm series has an integrable envelope controlling its full pointwise sum
-- statement:
--   Tonelli and finite-integral transfer for a series of integrable real-valued measurable functions. A summable sequence of L1 norms yields almost-sure absolute summability and an integrable envelope bounding every individual term. This is the reusable norm-series compactness ingredient for B24 gain increment convergence.
-- source:
--   Tonelli nonnegative-series theorem and Bochner integral norm summability, pinned Mathlib.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_integrable_norm_series_integrable_total_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (H : ℕ → Ω → ℝ)
    (hHI : ∀ k, Integrable (H k) P)
    (hSum : Summable (fun k => ∫ ω, ‖H k ω‖ ∂P)) :
    ∃ (B : Ω → ℝ),
      Integrable B P ∧
      (∀ᵐ ω ∂P, Summable (fun k => ‖H k ω‖) ∧ (∑' k, ‖H k ω‖) ≤ B ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖H k ω‖ ≤ B ω) := by sorry
