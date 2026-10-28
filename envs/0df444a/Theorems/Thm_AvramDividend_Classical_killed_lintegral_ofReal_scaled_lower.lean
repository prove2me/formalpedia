-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower
-- name    : AvramDividend.Classical.killed_lintegral_ofReal_scaled_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:41:35.722176+00:00
-- url     : https://prove2.me/theorems/1a199810-7d07-4330-8274-9fadc085c592
-- title:
--   Scale a killed first-passage lower expectation by any nonnegative payment
-- statement:
--   If the nonnegative-part expected value of a real payoff f on an event S dominates the real benchmark k, then multiplying the payoff and benchmark by any nonnegative payment size r preserves the lower expectation inequality. The result holds even when the payoff has not been shown measurable, using the ENNReal lower-integral constant-factor identity for finite scalars. In the barrier-dividend proof, it turns an ordinary two-sided q-exit discount estimate into the ε-sized killed first-record payment needed for the renewal base step.
-- source:
--   General ENNReal lower-integral constant multiplication and nonnegative Real-to-ENNReal embedding; bridge from the two-sided q-scale exit expectation to first dividend record budget.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real

open MeasureTheory Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_lintegral_ofReal_scaled_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (f : Ω → ℝ) (k r : ℝ)
    (hr : 0 ≤ r)
    (hbase : ENNReal.ofReal k ≤
      (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (f ω) else 0 ∂P)) :
    ENNReal.ofReal (r * k) ≤
      (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (r * f ω) else 0 ∂P) := by sorry
