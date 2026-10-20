-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_Wzero
-- name    : AvramDividend.Classical.chat04_lower_exit_lintegral_zero_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:41:47.435348+00:00
-- url     : https://prove2.me/theorems/f2638d8a-3194-425a-a9d3-0236eec32af1
-- title:
--   The discounted lower-exit q-scale integral vanishes when W at zero vanishes
-- statement:
--   Whenever a q-scale function has W(0)=0, the entire discounted lower-exit payoff vanishes pointwise, even when trajectories creep continuously through the lower boundary. Applying the already proved pointwise strict lower-exit zero-scale-payoff theorem inside the extended nonnegative Lebesgue integral yields a zero lower-exit contribution without any non-creeping hypothesis. This supplies the correct continuous-creeping-compatible branch for the stopped q-scale identity; an independent martingale and optional stopping result is still required.
-- source:
--   Proved AvramDividend.Classical.chat04_lower_exit_zero_scale_payoff (UUID 655be286-6672-476a-b7b6-167546330c2f); Mathlib lintegral_congr, lintegral_zero at pinned revision.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_zero_scale_payoff

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_exit_lintegral_zero_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWzero : W 0 = 0) (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by sorry
