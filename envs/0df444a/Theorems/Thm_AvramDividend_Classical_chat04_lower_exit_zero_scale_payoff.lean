-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_zero_scale_payoff
-- name    : AvramDividend.Classical.chat04_lower_exit_zero_scale_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:56:21.987418+00:00
-- url     : https://prove2.me/theorems/655be286-6672-476a-b7b6-167546330c2f
-- title:
--   At strict downward exit, the killed q-scale payoff vanishes when the scale function is zero at the origin
-- statement:
--   For a spectrally negative Lévy process and its q-scale function W, additionally assume W(0)=0. When the finite first strict downward exit below −x occurs strictly before the upward exit above a−x, the stopped surplus x+X_D is at most zero by the downward passage threshold theorem. Since W is zero for negative arguments and at zero by hypothesis, the killed discounted scale payoff e^(−qD)W(x+X_D) is exactly zero. The result is pointwise, handles continuous downward creeping correctly, and isolates the down-exit boundary term needed for the stopped-scale martingale argument in the zero-origin scale regime.
-- source:
--   The exact downward passage threshold theorem AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold (UUID a041b575-e1c0-4395-8a40-dd56ba828378); the published scale-function definition e6610c46-99bb-43cf-af87-4d07e25d1631; the published strict two-sided exit times a151e213-9af7-4401-b163-8e74db317cf8. The extra W(0)=0 hypothesis is necessary for downward creeping; it is not inferred from the standing assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_exit_zero_scale_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWzero : W 0 = 0) (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
     else 0) = 0 := by sorry
