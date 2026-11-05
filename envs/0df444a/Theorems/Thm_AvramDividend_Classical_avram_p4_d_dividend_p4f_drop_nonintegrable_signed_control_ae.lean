-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
-- name    : AvramDividend.Classical.avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:36:58.072214+00:00
-- url     : https://prove2.me/theorems/39a34110-32cc-46dd-9a1a-2dde789a0f94
-- title:
--   Original UBV P4-F budget drops nonintegrable nonpositive stopped dividend control pointwise a.e.
-- statement:
--   In the actual P4-F original τ, rightLimit-W, full paid Stieltjes Cash and discounted Term convention, any signed dividend remainder R that is a.e. nonpositive may be omitted from the right-hand side of the Itô budget even if R has no integrability proof. This permits P4-F to choose integrable H=0 for that control contribution, while retaining the genuinely integrable martingale and generator terms. Exact W/Cash/Term definitions are preserved; no new stochastic estimate is assumed.
-- source:
--   Original P4-F assembly Open declaration 1ba0679b-63d6-449f-90d2-d8a8a411655b; original residual 0dda1be7-9d8b-41e0-ae51-55fab5c38e22; elementary order under ∀ᵐ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mc Ms Ml G R : Ω → ℝ)
    (hRnonpos : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω := by sorry
