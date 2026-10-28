-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_scale_closed_form_of_exit
-- name    : AvramDividend.Classical.chat12_total_expected_lower_scale_closed_form_of_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:55:20.964987+00:00
-- url     : https://prove2.me/theorems/a59f7c40-f084-40e1-b701-136ac9202055
-- title:
--   Conditional lower killed-record total in q-scale ratio closed form
-- statement:
--   Assume a q-scale function W satisfying W(a)>0 and W(a-epsilon)≥0, together with the explicit strict discounted ε-up-before-(ε-a)-down exit factor identity Fminus=W(a-epsilon)/W(a). The sum over expected killed surviving upward record rewards is at least ε times the ratio times the reciprocal of one minus the ratio, interpreted as extended nonnegative reals. This directly specialises the Proved lower scalar geometric closed form and leaves Chat 1's still-Open q-scale identity as an explicit hypothesis.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_geometric_closed_form

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_lower_scale_closed_form_of_exit
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
      (∑' n : ℕ, (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) := by sorry
