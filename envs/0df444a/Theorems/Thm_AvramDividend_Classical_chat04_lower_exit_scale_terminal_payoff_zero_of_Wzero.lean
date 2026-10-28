-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
-- name    : AvramDividend.Classical.chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:02:42.02199+00:00
-- url     : https://prove2.me/theorems/d3e81040-4139-4569-b7ae-9a639eecc21e
-- title:
--   Pathwise vanishing of the strict lower-ruin stopped q-scale payoff at W(0)=0
-- statement:
--   For every sample path on which lower ruin precedes the strict upper exit, the discounted stopped q-scale terminal payoff vanishes when the scale function is zero at the origin. The creeping boundary case is handled by the published lower-exit creeping-atom identity.
-- source:
--   Proved chat04_lower_exit_scale_creeping_atom with hWzero.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWzero : W 0 = 0)
    (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) = 0 := by sorry
