-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_signed_stieltjes_mean_nonneg
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_stieltjes_mean_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:42:56.041665+00:00
-- url     : https://prove2.me/theorems/562afa07-1044-463b-ab21-f16578b97840
-- title:
--   Nonnegativity of original full stopped real signed Stieltjes expected dividends
-- statement:
--   For the original spectrally negative Levy process, its admissible strategy, the original dividendMeasure built from rightLimit, and the exact paymentTimes(ruinTime) intersection Iic T, the expected real discounted Stieltjes dividend is nonnegative for every q>=0 and T>=0. This is at exactly the same source, domain and measure as the ENNReal target, and explicitly provides the sign condition for ofReal and toReal conversions, including atom at time zero and continuous payments.
-- source:
--   Pointwise positivity of Real.exp and integral_nonneg twice, at the original Stieltjes dividend measure and probability P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_stieltjes_mean_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
