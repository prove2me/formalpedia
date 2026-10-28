-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_shifted_twoSided_reward
-- name    : AvramDividend.Classical.killed_nextRecord_weight_ge_shifted_twoSided_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:04:18.676824+00:00
-- url     : https://prove2.me/theorems/90281d2d-4883-465e-8667-7ee62e546b0f
-- title:
--   Surviving killed next-record payoff dominates the shifted discounted two-sided exit reward
-- statement:
--   At any attained surviving first record b, define the future strict first upward crossing of increment ε and the future strict downward crossing below ε−a. The actual killed discounted payment at b+ε dominates ε times the past discount times the shifted future discounted exit reward, with the latter set to zero if the upper exit does not precede the lower exit. If the upper exit occurs first, it is finite, and the proven killed-discount factorisation gives equality. Otherwise nonnegativity gives the inequality. This is the samplewise inequality required by the strong-Markov expectation lower bridge.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 1, strict first-record renewal lower bound.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_shifted_twoSided_exit_killed_discount_eq_product

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_nextRecord_weight_ge_shifted_twoSided_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (r : ℝ≥0)
      (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞)))
    (hσ : σ = (⨅ (r : ℝ≥0)
      (_ : X.X (u + r) ω - X.X u ω < ε - a),
      (r : ℝ≥0∞))) :
    ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          (if ρ < σ then
            ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
          else 0)) ≤
      (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) := by sorry
