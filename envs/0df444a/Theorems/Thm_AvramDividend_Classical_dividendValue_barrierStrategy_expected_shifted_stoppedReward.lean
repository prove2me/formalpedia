-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_expected_shifted_stoppedReward
-- name    : AvramDividend.Classical.dividendValue_barrierStrategy_expected_shifted_stoppedReward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:12:54.976809+00:00
-- url     : https://prove2.me/theorems/8810de34-7576-4d84-9b14-6391355aeb52
-- title:
--   Below-barrier expected dividends are the killed discounted shifted stopped reward
-- statement:
--   Starting from 0≤x≤a, the dividend value equals the expectation over paths where strict upper first passage wins against raw downward exit, of exp(-q u) times the discounted Stieltjes reward of Lévy increments after u over the exact translated original stopped-payment window. The finite time u is the coercion of the ENNReal upper-passage clock to NNReal; on unsuccessful paths this branch is never evaluated. This is the exact expectation-stage restart decomposition before applying strong Markov; it maintains the real stopping window without substituting the boundary expectation for a pathwise quantity.
-- source:
--   Proved event-restricted value identity abb0ce48, Proved pathwise shifted stopped window 1fff2edc, Proved future measure support a4f97533. Intermediate objective for the strong-Markov standing barrier value 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_rawTwoSidedExit_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendValue_barrierStrategy_expected_shifted_stoppedReward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ∫⁻ ω, if (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) < (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞)) then
        let u : ℝ≥0 := ((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal)
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          (∫⁻ t in Set.Ioi (0 : ℝ) ∩
            ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
              paymentTimes (ruinTime X x (barrierStrategy X x a) ω)),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂
              (dividendMeasure
                (fun r (_ : Ω) =>
                  sSup ((fun v : ℝ≥0 =>
                    X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
                ω))
      else 0 ∂P := by sorry
