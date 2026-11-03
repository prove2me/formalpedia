-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_spatial_localisation_vanishing_jump_error_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_spatial_localisation_vanishing_jump_error_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:04:56.226272+00:00
-- url     : https://prove2.me/theorems/351656c1-e377-4c9f-9a23-255bb32f9177
-- title:
--   Original ruin cash bound after spatial localisation and uniformly vanishing jump-truncation error
-- statement:
--   Starting with the source process X and original ruin/payment Stieltjes integral, a measurable increasing spatial-localisation cash sequence that almost surely covers the actual pre-ruin cash and whose expected bounds are no larger than budget plus every positive arbitrarily small error has full expected cash no larger than budget. This isolates jump truncation error passage without invoking uniform integrability and without asserting unsupported pathwise coverage. Covers cap-side and ruin-side localisation if the true a.e. exhaustion from W7-18 is supplied.
-- source:
--   Mathlib ENNReal.le_of_forall_pos_le_add and the W7-19 original-source spatial a.e. monotone exhaustion budget bridge. Source-specific endpoint atoms unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_spatial_localisation_vanishing_jump_error_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ k : ℕ, Measurable (LocalCash k))
    (hLocalMon : ∀ ω : Ω, Monotone (fun k : ℕ => LocalCash k ω))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ⨆ k : ℕ, LocalCash k ω)
    (budget : ℝ≥0∞)
    (hApprox : ∀ (k : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, LocalCash k ω ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
      budget := by sorry
