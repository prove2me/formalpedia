-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_real_horizon_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ruin_real_horizon_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:21:47.402807+00:00
-- url     : https://prove2.me/theorems/94bcacd7-6a61-4c52-bc75-c7ba8b114fd5
-- title:
--   Exact original full stopped real/ENNReal expected Stieltjes equality with canonical real horizon
-- statement:
--   For exact original spectrally negative Levy X, capped admissible strategy D, q>=0 and real time horizon T>=0, the full expected ruin-stopped double ENNReal discounted dividend payout on paymentTimes(ruinTime X x D omega) cap Iic T is exactly ENNReal.ofReal of the real expected discounted Stieltjes integral on the same stopped set against the same dividendMeasure. The expected real integral is integrable by the already accepted original process bridge. The type of T is precisely real, matching canonical BV/UBV targets; preserves the time-zero atom, all diffuse and interior jump payments and excludes positive ruin boundary. No BV/UBV hypothesis.
-- source:
--   Accepted W7-03 original deterministic horizon exact real/ENNReal expected bridge 633be7dd with NNReal horizon; Real.coe_toNNReal T hT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ruin_real_horizon_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
