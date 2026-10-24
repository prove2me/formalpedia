-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
-- name    : AvramDividend.Classical.discounted_stieltjes_lintegral_le_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:00:18.058198+00:00
-- url     : https://prove2.me/theorems/fc69051f-30bb-4e32-8f98-3ca0751d60fe
-- title:
--   Discounted Stieltjes dividend mass does not exceed undiscounted payment mass
-- statement:
--   For any nonnegative discount rate and an arbitrary measurable set of nonnegative payment times, the ENNReal Stieltjes integral of exp(-q t) is at most the measure of that payment set. This is valid even for infinite-mass measures and establishes pathwise finite-horizon dividend payout control as soon as local finiteness of the Stieltjes dividend measure is known.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.discounted_stieltjes_lintegral_le_measure
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (A : Set ℝ)
    (hAmeas : MeasurableSet A)
    (hAnonneg : ∀ t ∈ A, 0 ≤ t) :
    (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤ μ A := by sorry
