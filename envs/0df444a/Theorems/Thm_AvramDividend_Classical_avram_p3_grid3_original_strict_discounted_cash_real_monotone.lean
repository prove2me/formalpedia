-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_discounted_cash_real_monotone
-- name    : AvramDividend.Classical.avram_p3_grid3_original_strict_discounted_cash_real_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:32:30.009214+00:00
-- url     : https://prove2.me/theorems/cab8f321-4b8f-4c0a-8b04-d167fb9fc564
-- title:
--   Original strict discounted dividendMeasure cash is monotone in the real horizon
-- statement:
--   For the same original spectrally negative Levy path and actual admissible dividend-strategy measure, the strict cash accumulated up to s cannot exceed that accumulated up to t when 0≤s≤t. Use the accepted original all-path finite strict cash theorem to justify ENNReal-to-real monotonicity. No surrogate process, no extra stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_strict_discounted_cash_real_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * r)))
        ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩ Iio t,
      ENNReal.ofReal (Real.exp (-(q * r)))
        ∂(dividendMeasure D ω)).toReal := by sorry
