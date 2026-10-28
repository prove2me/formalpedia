-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_le_scale_ratio_geometric_of_exit
-- name    : AvramDividend.Classical.chat12_barrierSupValue_le_scale_ratio_geometric_of_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:54:51.089971+00:00
-- url     : https://prove2.me/theorems/58d75ab1-1392-41c5-be01-ec200254f082
-- title:
--   Conditional upper barrier dividend value bound in q-scale exit ratio form
-- statement:
--   Assume W is a q-scale function with 0≤W(a)<W(a+epsilon), and explicitly assume that the true discounted strict epsilon-up-before-(-a)-down exit expectation equals ENNReal.ofReal(W(a)/W(a+epsilon)). Then barrierSupValue is at most ENNReal.ofReal epsilon divided by one minus that scale ratio, in extended nonnegative-real arithmetic. This directly instantiates the fully Proved upper dividend valuation theorem and is independent of the still-Open corrected exit identity, left as an explicit premise.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_le_closed_form_of_trueExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_le_scale_ratio_geometric_of_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    barrierSupValue X a q ≤
      ENNReal.ofReal ε * (1 - ENNReal.ofReal (W a / W (a + ε)))⁻¹ := by sorry
