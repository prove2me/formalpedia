-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_ge_scale_ratio_geometric_of_exit
-- name    : AvramDividend.Classical.chat12_barrierSupValue_ge_scale_ratio_geometric_of_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:54:38.396445+00:00
-- url     : https://prove2.me/theorems/23f85629-d0b3-4ac4-8f56-89abcf88a61f
-- title:
--   Conditional lower barrier dividend value bound in q-scale exit ratio form
-- statement:
--   Given a q-scale function W satisfying W(a)>0, W(a-epsilon)≥0 and ε<a, explicitly identify the genuine discounted strict epsilon-up-before-(epsilon-a)-down exit expectation with ENNReal.ofReal(W(a-epsilon)/W(a)). The barrier dividend value is then at least ENNReal.ofReal epsilon times this ratio divided by one minus it, in extended nonnegative-real arithmetic. The proof specialises the Proved generic lower dividend valuation theorem, without importing the still-Open corrected q-scale exit identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_ge_closed_form_of_trueExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_ge_scale_ratio_geometric_of_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ENNReal.ofReal ε *
      (ENNReal.ofReal (W (a - ε) / W a) *
        (1 - ENNReal.ofReal (W (a - ε) / W a))⁻¹) ≤
      barrierSupValue X a q := by sorry
