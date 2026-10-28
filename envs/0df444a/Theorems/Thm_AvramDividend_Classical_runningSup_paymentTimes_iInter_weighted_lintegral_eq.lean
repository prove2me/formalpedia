-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_weighted_lintegral_eq
-- name    : AvramDividend.Classical.runningSup_paymentTimes_iInter_weighted_lintegral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:12:31.012072+00:00
-- url     : https://prove2.me/theorems/53355d4e-bf28-4bf3-a031-44c6f4198619
-- title:
--   Weighted Stieltjes reward is unaffected by the terminal endpoint in shrinking dividend-payment windows
-- statement:
--   For every nonnegative, possibly nonintegrable reward weight and any countable sequence of payment horizons, integrating against the reflected running-supremum Stieltjes dividend measure over the intersection of strict payment windows equals integration over the payment window at the infimum horizon. The previously proved equality of restricted Stieltjes measures transfers to every weighted nonnegative integral, including exponential dividend discounting. No finiteness assumption is required for this endpoint identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3, Proposition 1, https://arxiv.org/pdf/math/0702893; Prove2Me theorem eff1caea-3ef6-43d9-9835-4fe1ffebf19b.

import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Stieltjes reward integrals agree on the limiting payment window and the
    intersection of decreasing payment windows, for every nonnegative weight. -/
theorem runningSup_paymentTimes_iInter_weighted_lintegral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in (⋂ n, paymentTimes (σ n)), f t
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in paymentTimes (⨅ n, σ n), f t
      ∂(dividendMeasure (runningSup X) ω)) := by sorry

end AvramDividend.Classical
