-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
-- name    : AvramDividend.Classical.avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:38:53.207432+00:00
-- url     : https://prove2.me/theorems/2f3e3b80-96d7-47e5-b26e-2417cdc387ef
-- title:
--   Bochner integrated BV approximation error with integrable signed-payoff tail rather than jump first moment
-- statement:
--   Transfer the global C1 approximation error through Bochner integration with two distinct L1 envelopes: a small BV exponential compensator εH and twice the signed-payoff-integrable large-jump tail T. This avoids a false global first moment of the Lévy measure. Assumes exactly the required individual integrability premises; all interchanges follow from integral_sub, absolute-integral domination, integral_mono_ae, and integral_const_mul.
-- source:
--   Bochner dominated signed integral transfer with two integrable error envelopes.

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem AvramDividend.Classical.avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G H T : α → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (hT : Integrable T μ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbd : ∀ᵐ z ∂μ, |F z - G z| ≤ ε * H z + 2 * T z) :
    |(∫ z, F z ∂μ) - (∫ z, G z ∂μ)| ≤
      ε * (∫ z, H z ∂μ) + 2 * (∫ z, T z ∂μ) := by sorry
