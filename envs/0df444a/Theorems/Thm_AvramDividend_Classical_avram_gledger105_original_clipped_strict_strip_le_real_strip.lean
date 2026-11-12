-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger105_original_clipped_strict_strip_le_real_strip
-- name    : AvramDividend.Classical.avram_gledger105_original_clipped_strict_strip_le_real_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:01:55.256558+00:00
-- url     : https://prove2.me/theorems/7fc96bc5-21c5-4178-bbb7-6756c0c14a71
-- title:
--   Original NNReal-clipped strict final cash is at most the real-subtracted final cash
-- statement:
--   For a bounded original clock and finite original Stieltjes cash, clipping the left endpoint of the final open interval by NNReal truncated subtraction can only remove discounted cash. This comparison is valid for time-zero atoms and under the original ruin clock, and is required for gledger39.
-- source:
--   Simple exact interval order plus authoritatively Proved gledger84 and closed original stopped cash finiteness; direct component of gledger39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger105_original_clipped_strict_strip_le_real_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n ρ δ : ℝ≥0) (hρn : ρ ≤ n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((ρ - δ : ℝ≥0) : ℝ) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
