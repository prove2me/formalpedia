-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:06:25.172188+00:00
-- url     : https://prove2.me/theorems/2b209825-ff7a-4c53-9e4e-2425e44b6d2c
-- title:
--   Original strict pre-ruin closed-prefix real Stieltjes integral equals exact ENNReal dividend payout
-- statement:
--   For the canonical original spectrally negative Lévy process X and actual nondecreasing left-continuous dividend strategy D, at an arbitrary path ω and any clock S=0 or strictly before ruin, the complete discounted original Stieltjes payout on paymentTimes(ruinTime) intersect Iic S equals ENNReal.ofReal of the ordinary real integral over Icc(0,S). The original measure of that closed interval is ENNReal.ofReal(rightLimit D S ω), always finite, so this is an exact same-measure equality. It includes the initial right-payment atom, any terminal right jump strictly before ruin, all intermediate jumps, and continuous or singular-continuous dividends. It does not include positive ruin-boundary payments.
-- source:
--   Original canonical dividend definitions 561c1e83. Proved exact original stopped region equality bfe4a214, original closed interval mass d6ace15b, and finite-measure discounted real/ENNReal equality 72bc55bf. For q≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (S : ℝ≥0)
    (hPre : S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in Icc (0 : ℝ) (S : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
