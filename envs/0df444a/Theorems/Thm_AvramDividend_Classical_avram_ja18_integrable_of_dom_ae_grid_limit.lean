-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_integrable_of_dom_ae_grid_limit
-- name    : AvramDividend.Classical.avram_ja18_integrable_of_dom_ae_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:29:36.173196+00:00
-- url     : https://prove2.me/theorems/470a6b58-7010-4f8c-b1ce-6d30cd84fa61
-- title:
--   An original stopped reward limit is integrable under the common source envelope
-- statement:
--   An almost sure limit of integrable finite-grid reward functions is integrable whenever the limiting original reward is dominated by one integrable envelope. The limit inherits almost-everywhere measurability from the grid sequence, and the envelope gives its L1 bound.
-- source:
--   Independent genuinely simpler L1 limiting child needed to close 2d92580d from finite-range optional sampling; handles endpoint integrability separately from conditional expectation stability.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_integrable_of_dom_ae_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (J : ℕ → Ω → ℝ) (Z B : Ω → ℝ)
    (hInt : ∀ k, Integrable (J k) P)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (Z ω)))
    (hBInt : Integrable B P)
    (hBound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ B ω) :
    Integrable Z P := by sorry
