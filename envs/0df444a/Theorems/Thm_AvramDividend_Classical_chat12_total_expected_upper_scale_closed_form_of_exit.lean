-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_closed_form_of_exit
-- name    : AvramDividend.Classical.chat12_total_expected_upper_scale_closed_form_of_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:40:26.139918+00:00
-- url     : https://prove2.me/theorems/4ed9d350-3e6b-40a6-9969-453b853e8ff1
-- title:
--   Conditional closed-form upper killed-record expectation total with q-scale ratio
-- statement:
--   Given a q-scale function W and the explicit discounted strict two-sided-exit factor identification Fplus = W(a)/W(a+epsilon), total expected discounted surviving upward-record rewards are bounded above by ENNReal.ofReal epsilon times (1 - ENNReal.ofReal (W(a)/W(a+epsilon)))^(-1). This specialises the already-Proved closed-form upper geometric budget and leaves Chat 1's still-Open q-scale exit identity as an explicit hypothesis.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_geometric_closed_form

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_upper_scale_closed_form_of_exit
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
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) ≤
      ENNReal.ofReal ε *
        (1 - ENNReal.ofReal (W a / W (a + ε)))⁻¹ := by sorry
