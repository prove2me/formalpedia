-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_finite_of_trueExit_factor
-- name    : AvramDividend.Classical.chat12_barrierSupValue_finite_of_trueExit_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:12:41.535785+00:00
-- url     : https://prove2.me/theorems/14f42cc2-7c1d-4e8e-b214-34679400e887
-- title:
--   Finite dividend barrier value from strict exit factor below one
-- statement:
--   Let X be a standing spectrally negative Lévy process and q,a,epsilon>0. If the true discounted strict upward-before-(-a)-downward exit expectation equals ENNReal.ofReal p for 0≤p<1, then the barrier strategy value barrierSupValue X a q is finite in ENNReal. This uses the Proved pathwise dividend Stieltjes upper bound by killed record rewards, Proved expected value upper sum, and Proved finiteness of the total expected killed-record payments. It does not require the Open q-scale-function exit identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_finite_of_trueExit_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_finite_of_trueExit_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p < 1)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    barrierSupValue X a q < ∞ := by sorry
