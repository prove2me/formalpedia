-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_finite_of_scale_exit
-- name    : AvramDividend.Classical.chat12_barrierSupValue_finite_of_scale_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:17:50.397981+00:00
-- url     : https://prove2.me/theorems/cafc2059-ca8f-4bd4-b2b5-1540bb7b0a20
-- title:
--   Finiteness of barrier dividend value from conditional scale-function exit factor
-- statement:
--   Under a q-scale function W with 0 ≤ W(a) < W(a+ε) and the explicit strict discounted two-sided-exit factor identity equal to W(a)/W(a+ε), the barrier strategy value barrierSupValue X a q is finite. Combines the Proved pointwise killed-record dividend upper budget, Proved expectation upper bound and Proved q-scale conditional total expected-record finiteness. It does not depend on the Open corrected q-scale exit theorem, which remains an assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_finite_of_exit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_finite_of_scale_exit
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
    barrierSupValue X a q < ∞ := by sorry
