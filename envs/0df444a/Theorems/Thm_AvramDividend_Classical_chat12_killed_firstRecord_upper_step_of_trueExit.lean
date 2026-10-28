-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_upper_step_of_trueExit
-- name    : AvramDividend.Classical.chat12_killed_firstRecord_upper_step_of_trueExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:41:54.66237+00:00
-- url     : https://prove2.me/theorems/3585a9cc-4d22-4b13-86d8-5cbdb5638d11
-- title:
--   Upper killed-record q-factor step from an explicit strict-exit expectation identity
-- statement:
--   Given a real candidate p and the explicit hypothesis that the discounted strict upward-before-downward exit expectation equals ENNReal.ofReal p, the expected killed next upward-record reward is at most ENNReal.ofReal p times the previous record reward. This theorem follows immediately from the already Proved upper strong-Markov one-cycle expectation inequality, without any scale-function existence or two-sided-exit ratio theorem. It separates the stochastic restart mechanism from identifying the factor.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_firstRecord_upper_step_of_trueExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (p : ℝ)
    (hExit : (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p)
    (n : ℕ) :
    (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
      ENNReal.ofReal p * (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
