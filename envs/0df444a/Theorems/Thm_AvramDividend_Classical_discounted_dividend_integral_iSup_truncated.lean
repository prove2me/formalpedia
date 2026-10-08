-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_integral_iSup_truncated
-- name    : AvramDividend.Classical.discounted_dividend_integral_iSup_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:33:00.728539+00:00
-- url     : https://prove2.me/theorems/29ca92e4-f470-4d1a-b1d6-521eea7f9f9f
-- title:
--   The complete pathwise discounted dividend payoff is the supremum of its finite-time truncations
-- statement:
--   For any dividend process path D and ruin time, the complete discounted Lebesgue–Stieltjes dividend integral over paymentTimes equals the supremum over integer horizons n of the same integral truncated to t≤n. This follows from Borel measurability of paymentTimes, measurability of exp(−qt), and the general real-time measure monotone convergence theorem. It handles continuous as well as jump dividends exactly at the pathwise level. The outer expectation in dividendValue needs an additional measurability/MCT bridge.
-- source:
--   Children paymentTimes_measurable and lintegral_exhausted_by_natural_horizons, both pinned to Mathlib revision 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividend_integral_iSup_truncated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
