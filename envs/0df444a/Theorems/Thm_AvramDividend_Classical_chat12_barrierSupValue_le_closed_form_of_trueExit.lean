-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_le_closed_form_of_trueExit
-- name    : AvramDividend.Classical.chat12_barrierSupValue_le_closed_form_of_trueExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:10:53.655036+00:00
-- url     : https://prove2.me/theorems/b6a07b6b-e3a9-40f0-a921-499b4e5cf543
-- title:
--   Barrier value upper renewal bound from explicit strict exit factor
-- statement:
--   For a spectrally negative Lévy process and strictly positive q,a,epsilon, assume the discounted strict epsilon-up-before-(-a)-down exit expectation is ENNReal.ofReal p, p≥0. Then the barrier strategy's discounted dividend value at the barrier is at most epsilon times the extended-real geometric reciprocal (1-p)^{-1}. This connects the already Proved pathwise domination of stopped dividend Stieltjes rewards by killed first-record sums, the Proved expectation Tonelli budget, and the Proved closed-form total expected first-record inequality. It does not invoke the still-Open corrected q-scale exit identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_geometric_closed_form

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_le_closed_form_of_trueExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    barrierSupValue X a q ≤
      ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by sorry
