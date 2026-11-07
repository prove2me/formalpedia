-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_prefix_mono_finite
-- name    : AvramDividend.Classical.avram_a19_discounted_cash_prefix_mono_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:21:03.361727+00:00
-- url     : https://prove2.me/theorems/c5b920a3-575a-4731-b30d-0d8e8b7a6e5f
-- title:
--   Original finite discounted Stieltjes cash is monotone in strict horizon
-- statement:
--   For the actual original dividend Stieltjes measure, finite discounted cash on the strict payment interval before s is at most finite discounted cash before T whenever s ≤ T. The full-horizon finiteness hypothesis prevents the usual ENNReal.toReal infinity degeneracy.
-- source:
--   Exact horizon-monotonicity step in Avram original BV positive-horizon prebudget a19d8b28; applicable independently to finite-cap and top-cap source branches.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_discounted_cash_prefix_mono_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (q s T : ℝ) (hst : s ≤ T)
    (hFin :
      (∫⁻ t in paymentTimes σ ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤) :
    (∫⁻ t in paymentTimes σ ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes σ ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
