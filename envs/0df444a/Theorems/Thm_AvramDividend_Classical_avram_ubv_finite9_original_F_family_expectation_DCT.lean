-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_expectation_DCT
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_F_family_expectation_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:05:58.553713+00:00
-- url     : https://prove2.me/theorems/4c47ac2a-7160-47a7-ad04-1a50d3a81e77
-- title:
--   Dominated convergence of original finite-cap stopped value-plus-cash expectations
-- statement:
--   Using the proved source-exact common integrable F family envelope for finite C and closed-clock cash, any almost-everywhere convergent measurable localisation Fk has convergent original expectations. This is the unmodified source payoff, including right-payment, final-clock and time-zero atoms, and is the optional-stopping localisation-limit stage rather than the Ito-Meyer drift identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_F_family_expectation_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ (L : Ω → ℝ),
      (∀ k, AEStronglyMeasurable (F k) P) →
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (L ω))) →
      Tendsto (fun k => ∫ ω, F k ω ∂P) atTop (𝓝 (∫ ω, L ω ∂P)) := by sorry
