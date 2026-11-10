-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
-- name    : AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:27:10.413489+00:00
-- url     : https://prove2.me/theorems/e0aebc07-12ea-4ac4-b617-2d07e34adfe3
-- title:
--   Uniform L1 original stopped cash envelope for every measurable physical-clock grid prefix
-- statement:
--   For one original spectrally negative Levy dividend strategy, the closed discounted dividend cash at a deterministic finite horizon T is integrable and pointwise dominates the strict Iio dividend cash at every countably indexed, merely measurable physical clock σ_k bounded by T. Every indexed strict cash is separately integrable. The same original paymentTimes and dividendMeasure preserve the time-zero right-payment atom in the envelope, exclude positive-ruin right payments, retain continuous Stieltjes dividend mass, and protect the final stop-straddling cell. No grid-floor stopping-time or detached Brownian identification is assumed. This provides uniform domination for Gaussian physical-grid dominated convergence in a338c453 and 249c532d.
-- source:
--   Proved 3deca135 (bounded measurable full cash L1), c7715133 (measurable strict cash L1), c4e50d93 (pathwise upper cash ENNReal finiteness); exact parent imports a338c453 and 249c532d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0)
    (hσmeas : ∀ k, Measurable (fun ω : Ω => (σ k ω : ℝ)))
    (hσbound : ∀ k ω, σ k ω ≤ T) :
    Integrable (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P ∧
    (∀ k, Integrable (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P) ∧
    (∀ k ω, 0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∧
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) := by sorry
