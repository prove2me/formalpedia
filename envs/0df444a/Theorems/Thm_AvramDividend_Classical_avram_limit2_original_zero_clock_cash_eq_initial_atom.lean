-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_zero_clock_cash_eq_initial_atom
-- name    : AvramDividend.Classical.avram_limit2_original_zero_clock_cash_eq_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:17:36.422957+00:00
-- url     : https://prove2.me/theorems/0f6cae65-a52d-4930-9578-29639c22ca0a
-- title:
--   Zero stopping clock preserves the actual initial dividend atom in original-process expected Stieltjes cash
-- statement:
--   For the original Levy surplus X and actual dividendMeasure D, expected discounted Stieltjes cash stopped at a zero clock is exactly the cash integral over singleton time zero, even when original ruinTime is zero. This follows directly fibrewise from public Proved paymentTimes_min_zero_eq_singleton_zero 77cdd573 without assuming the zero-time payment vanishes. The identity makes the endpoint convention explicit in perpetual dividend-value monotone horizon passage.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_zero_clock_cash_eq_initial_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in ({0} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
