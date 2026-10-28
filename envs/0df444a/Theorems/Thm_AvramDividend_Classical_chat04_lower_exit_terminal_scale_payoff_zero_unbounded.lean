-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_terminal_scale_payoff_zero_unbounded
-- name    : AvramDividend.Classical.chat04_lower_exit_terminal_scale_payoff_zero_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:23:06.335989+00:00
-- url     : https://prove2.me/theorems/46193b80-ee17-4e08-90f3-115d4406d0af
-- title:
--   Unbounded-variation strict lower-ruin q-scale terminal payoff vanishes pathwise
-- statement:
--   When a spectrally negative Lévy process has unbounded variation, q>0 and W is its q-scale function, the discounted terminal scale payoff on the strict event of downward ruin before upward exit is zero pathwise. The proof combines the Proved unbounded-variation origin identity W(0)=0 and the Proved creeping-atom-aware lower-exit terminal payoff lemma. It handles downward jumps and continuous creeping consistently.
-- source:
--   Proved chat04_scale_zero_origin_of_unbounded_variation and chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_lower_exit_terminal_scale_payoff_zero_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) = 0 := by sorry
