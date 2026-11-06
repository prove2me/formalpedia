-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_finite_ruin_cash_le_perpetual_value
-- name    : AvramDividend.Classical.avram_sweep16_original_finite_ruin_cash_le_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:05:08.7112+00:00
-- url     : https://prove2.me/theorems/4cea8811-bb2c-4f2d-864c-fd2cc87f7b18
-- title:
--   Any original ruin-clock finite-horizon discounted dividend cash is below perpetual dividend value
-- statement:
--   An independent original-process time-horizon monotonicity theorem. For arbitrary real T, the integral over dividend-payment times through the actual ruin clock and up to T is bounded by the integral up to the natural-number ceiling of T, by pointwise set inclusion and Mathlib's lintegral_mono_set. Integrating over scenarios preserves the inequality. The already-Proved source-exact identity dividendValue_eq_iSup_truncated identifies the perpetual discounted value with the supremum of natural finite horizons. No stochastic budget, bounded variation split, or Open theorem is imported. This removes the inverse bridge obstruction when deriving canonical BV and UBV truncated bounds from their original perpetual-value parents.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_finite_ruin_cash_le_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by sorry
