-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
-- name    : AvramDividend.Classical.avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:11:21.153339+00:00
-- url     : https://prove2.me/theorems/e0a34e97-9144-43ea-a506-3de6e7680e0c
-- title:
--   Original stopped dividend payment domain is exactly unchanged under a cap beyond the finite horizon, including zero and infinite ruin
-- statement:
--   For the actual spectrally negative Lévy source process X and admissible strategy D, if the extended nonnegative truncation a strictly exceeds the nonnegative real horizon T, then for every path including ruinTime zero and infinity the restricted payment-time sets agree exactly: paymentTimes(min(ruinTime,a))∩Iic T=paymentTimes(ruinTime)∩Iic T. The definition paymentTimes σ includes time zero unconditionally and positive times only strictly before σ. No boundary smoothness, bounded variation, stopping-time filtration enlargement, or Stieltjes integration is used; the result is set theoretic and supports a single bounded-clock budget transfer.
-- source:
--   Exact original paymentTimes and ruinTime definitions in AvramDividend.Classical; corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ≥0∞) (hTa : ENNReal.ofReal T < a) :
    ∀ ω, paymentTimes (min (ruinTime X x D ω) a) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iic T := by sorry
