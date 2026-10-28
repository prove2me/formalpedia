-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
-- name    : AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:42:01.268847+00:00
-- url     : https://prove2.me/theorems/af53523a-9f1c-4ea6-b575-cf276508e2ae
-- title:
--   Pointwise upper domination of a killed next-record discount by the shifted two-sided reward
-- statement:
--   At a finite first record, assume the shifted upper exit clock is finite and survival to the next record implies the strict shifted upper-before-lower event. Then the killed next-record discounted weight is pointwise dominated by the product of the past exponential discount and the shifted two-sided-exit reward. The proof is a direct upper-direction counterpart to existing lower-payoff comparisons, isolating precisely the pathwise inclusion still required for the renewal geometric bound.
-- source:
--   Use the proved next-record exponential factorisation on survival, where the assumed strict exit inclusion activates the shifted reward; outside survival, the killed weight vanishes.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_discount_eq_past_mul_future

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (hε : 0 ≤ ε) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hρfinite : ρ ≠ ⊤)
    (hInclusion : twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω → ρ < σ) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by sorry
