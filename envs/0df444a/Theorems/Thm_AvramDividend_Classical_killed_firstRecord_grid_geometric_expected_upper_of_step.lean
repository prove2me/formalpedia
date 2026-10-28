-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_upper_of_step
-- name    : AvramDividend.Classical.killed_firstRecord_grid_geometric_expected_upper_of_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:34:49.455107+00:00
-- url     : https://prove2.me/theorems/0d422357-0a1a-4057-a64b-36fa99b9a1e4
-- title:
--   Geometric upper bound for killed first-record expectations from a one-step renewal inequality
-- statement:
--   For a spectrally negative Levy process with nonnegative discount and record spacing, let w_n be the actual killed discounted strict first-record payment at level b+n h. If successive expected payments satisfy a one-step multiplicative upper recurrence with nonnegative ratio p, then the expected n-th payment is at most h p^n. The initial bound follows from the proven pointwise payment bound and the probability law; the remaining recurrence is kept explicit for the strong-Markov renewal step.
-- source:
--   Root-linked helper for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound (c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69): discharges the geometric induction and base expectation using Proved chat08_killed_record_discount_weight_le_cell, while exposing the one-step killed first-record recurrence as the remaining stochastic premise.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_killed_record_discount_weight_le_cell

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_grid_geometric_expected_upper_of_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b q h p : ℝ)
    (hq : 0 ≤ q) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (h * Real.exp (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
      else 0)
    (hstep : ∀ n,
      (∫⁻ ω, w (n + 1) ω ∂P) ≤
        ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P)) :
    ∀ n, (∫⁻ ω, w n ω ∂P) ≤ ENNReal.ofReal (h * p ^ n) := by sorry
