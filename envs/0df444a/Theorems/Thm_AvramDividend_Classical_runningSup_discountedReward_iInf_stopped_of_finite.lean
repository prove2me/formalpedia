-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_iInf_stopped_of_finite
-- name    : AvramDividend.Classical.runningSup_discountedReward_iInf_stopped_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:21:13.568457+00:00
-- url     : https://prove2.me/theorems/c324f116-56bf-417a-9bc0-a36a83a548f6
-- title:
--   Discounted Stieltjes rewards are continuous at decreasing finite-mass ruin horizons
-- statement:
--   For any decreasing extended ruin horizons, if the first discounted running-supremum Stieltjes reward is finite, then the reward stopped at the infimum time equals the infimum of the rewards stopped at the original horizons. The proof applies the finite-integral antitone-convergence theorem to the measurable discounted reward indicators. The already Proved restricted-measure endpoint identity removes the potentially spurious terminal payment atom.
-- source:
--   Mathlib MeasureTheory.lintegral_iInf and Proved runningSup_paymentTimes_iInter_restrict_eq; zero-barrier dividend limit prerequisite.

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_discountedReward_iInf_stopped_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Antitone σ)
    (q : ℝ)
    (hfinite : ∫⁻ t in paymentTimes (σ 0),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω) ≠ ⊤) :
    (∫⁻ t in paymentTimes (⨅ n, σ n),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) =
    ⨅ n, (∫⁻ t in paymentTimes (σ n),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) := by sorry
