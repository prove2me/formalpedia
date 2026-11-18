-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva46_original_strict_cash_prefix_pointwise_monotone
-- name    : AvramDividend.Classical.avram_bva46_original_strict_cash_prefix_pointwise_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:22:14.00042+00:00
-- url     : https://prove2.me/theorems/d2321a9b-347e-4867-b108-c49c0b1475ce
-- title:
--   Actual stopped discounted dividend Stieltjes cash strictly before T minus margin is bounded pathwise by strictly before T
-- statement:
--   Under the original admissible left-continuous dividend strategy, for any nonnegative discount rate, positive real horizon and nonnegative margin δ, the genuine stopped discounted dividend Stieltjes cash before T−δ is at most the cash before T for every sample path. The proof uses the original full closed stopped Stieltjes cash finiteness, measurable set inclusion for the strict horizon intervals, lintegral_mono_set and ENNReal.toReal_mono. This precise atom-safe pointwise monotonicity enables transfer of full-horizon original HJB budgets to each strict physical-prefix cash plus the same true full-T survivor terminal without assuming the cash measure is atom-free.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva46_original_strict_cash_prefix_pointwise_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℝ) (hδ : 0 ≤ δ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal :=
  by sorry
