-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_global_shifted_twoSided_upper
-- name    : AvramDividend.Classical.killed_nextRecord_discount_global_shifted_twoSided_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:06:25.836968+00:00
-- url     : https://prove2.me/theorems/1f8c1058-f4f2-4fb3-bcea-5ad6ce1cfd53
-- title:
--   Global pointwise killed-record domination by the shifted two-sided reward
-- statement:
--   At every sample path, the stopped higher-record discounted payoff is dominated by the first-record discount times the shifted two-sided-exit discounted payoff, with the finite first record represented using ENNReal.toNNReal. On survival the earlier and higher first-passage clocks have finite witnesses and the full killed-record comparison applies; off survival the killed payoff vanishes. This eliminates the witness premises from the renewal pathwise bound.
-- source:
--   Split on survival of the higher record. On survival obtain finite adjacent clocks and their delay, identify the earlier witness with ENNReal.toNNReal, rewrite the shifted infima, and invoke the verified killed-record upper bound. Off survival the killed payoff is zero.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_discount_global_shifted_twoSided_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞))) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q *
        ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by sorry
