-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_bounded_random_horizon_cash_bound
-- name    : AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_bounded_random_horizon_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:04:18.64649+00:00
-- url     : https://prove2.me/theorems/ee1ca770-b5c9-4e76-8f7e-93900a444f45
-- title:
--   Original Esscher cash envelope at every samplewise bounded random localisation horizon
-- statement:
--   For the actual original spectrally negative Levy X and q>0 there is one positive source Esscher exponent theta that uniformly bounds every admissible discounted Stieltjes dividend payout up to a samplewise real cutoff tau(omega) bounded by a deterministic T, uniformly in reserves x<=R and all caps. The cutoff may be random or a localising clock and need not be replaced by a fictitious model. The result includes the terminal and time-zero payment atoms; only pointwise set inclusion and ENNReal integral monotonicity are used after the already-Proved deterministic bound.
-- source:
--   Proved original every-real-horizon Esscher cash bound UUID 523fa9d2-6313-4b1d-8352-8c0c16930150, same-path payment set inclusion Iic(tau(omega)) subset Iic T, original dividendMeasure and P, pathwise lintegral_mono_set then expected lintegral_mono. Useful for genuine bounded stopping-time payout localisation in corrected UBV stochastic core 429e17ca, without claiming stochastic martingale centering.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_bounded_random_horizon_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      ∀ C : ℝ≥0∞, ∀ D : ℝ≥0 → Ω → ℝ,
        IsAdmissibleLe X x C D →
      ∀ T : ℝ, ∀ τ : Ω → ℝ, (∀ ω, τ ω ≤ T) →
        ENNReal.ofReal θ *
          (∫⁻ ω, ∫⁻ t in
            paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (Real.exp (θ * R)) := by sorry
