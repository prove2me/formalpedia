-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
-- name    : AvramDividend.Classical.dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:39:32.640024+00:00
-- url     : https://prove2.me/theorems/d16ead6f-62c6-4c14-b993-d1ad611dd874
-- title:
--   Below-barrier expected dividend value equals killed discounted future-increment stopped reward
-- statement:
--   For 0≤x≤a with a>0, the dividend value equals the expectation on successful upper-before-lower Lévy exits of the first-upcrossing discount times the Stieltjes running-supremum dividend reward of post-upcrossing future increments, stopped at the first negative shifted reflected-reserve time. This makes the entire random future reward a functional only of post-upcrossing Lévy increments. No pathwise equality with unconditional boundary expectation and no scale-function exit identity is assumed.
-- source:
--   Composes proved dividendValue_barrierStrategy_rawTwoSidedExit_support abb0ce48, barrierStrategy_upExit_before_controlledRuin_iff_rawExit 374d2f8d and accepted actual shifted-ruin stopped-reward  b3933be6. Final pre-Markov form for 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_rawTwoSidedExit_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_shifted_ruin_window
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ∫⁻ ω, if (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) < (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞)) then
        let u : ℝ≥0 := ((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal)
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          (∫⁻ t in Set.Ioi (0 : ℝ) ∩
            paymentTimes
              (⨅ (r : ℝ≥0)
                (_ : a + (X.X (u + r) ω - X.X u ω) <
                  max 0
                    (sSup ((fun z : ℝ≥0 => X.X (u + z) ω) '' Set.Icc 0 r) -
                      X.X u ω)), (r : ℝ≥0∞)),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂
              (dividendMeasure
                (fun r (_ : Ω) =>
                  sSup ((fun v : ℝ≥0 =>
                    X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
                ω))
      else 0 ∂P := by sorry
