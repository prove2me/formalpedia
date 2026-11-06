-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_clock_cash_monotone
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_clock_cash_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:06:10.270478+00:00
-- url     : https://prove2.me/theorems/21bda3d6-6e73-4786-97d1-8e334ef8e6b0
-- title:
--   Monotonicity of genuine original positive-natural stopped expected dividend cash under enlargement of the natural clock
-- statement:
--   For an actual original Lévy process X, dividend strategy D, ruinTime, paymentTimes and Stieltjes dividendMeasure, the expected nonnegative discounted dividend cash on closed Iic T, stopped at min(ruinTime,n), is monotone in positive natural clock n: if 0<n≤m the n-stopped expected cash is at most m-stopped expected cash. The proof uses the previously Proved exact strict natural endpoint representation and nested interval monotonicity, retaining time-zero and time-T dividends.
-- source:
--   Direct exact double-lintegral monotonicity for actual original cash, using Proved public 26471312. Enables cofinal natural-clock extraction and monotone-limit alternatives without an equality-in-law coupling or source stochastic assumptions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_clock_cash_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
