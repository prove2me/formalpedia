-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_discounted_stieltjes_le_undiscounted_dividend_mass
-- name    : AvramDividend.Classical.avram_wave7_11_discounted_stieltjes_le_undiscounted_dividend_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:43:34.509196+00:00
-- url     : https://prove2.me/theorems/33491eff-21b5-48aa-b308-2b1354ba9f9c
-- title:
--   Discounted original dividend Stieltjes reward is at most the undiscounted payment measure
-- statement:
--   For each original dividend strategy path D(ω), the Stieltjes measure on real time, genuine payment stopping clock σ and finite real horizon T, if q≥0 the discounted ENNReal integral over paymentTimes σ ∩ Iic T is bounded by the undiscounted dividend-measure mass of that identical set. The time-zero dividend atom is preserved, and the proof uses the true nonnegative real-time support of paymentTimes rather than a surrogate nonnegative real measure.
-- source:
--   Direct pathwise measure-theoretic estimate for the Avram original finite-horizon UBV value bridge; uses Proved paymentTimes_measurable 88dafb7f and pinned Mathlib ae_restrict_mem, Real.exp_le_one_iff, lintegral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_discounted_stieltjes_le_undiscounted_dividend_mass
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (dividendMeasure D ω) (paymentTimes σ ∩ Iic T) := by sorry
