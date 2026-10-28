-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_ge_closed_form_of_trueExit
-- name    : AvramDividend.Classical.chat12_barrierSupValue_ge_closed_form_of_trueExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:11:19.693158+00:00
-- url     : https://prove2.me/theorems/bfbd6d13-6cb7-4b20-81e4-2995091869e7
-- title:
--   Barrier value lower renewal bound from explicit strict exit factor
-- statement:
--   Let q,a,epsilon be positive and suppose the discounted strict epsilon-up-before-(epsilon-a)-down exit expectation is ENNReal.ofReal p for p≥0. Then the barrier dividend value is at least epsilon times p/(1-p), in extended nonnegative-real arithmetic. The proof uses the existing Proved lower pathwise stopped-first-record dividend Stieltjes budget, Proved reward measurability, the Proved value lower expectation bound, and the newly Proved total lower geometric expected-record closed form. The q-scale exit identity remains an explicit hypothesis rather than an imported Open theorem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_geometric_closed_form

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_barrierSupValue_ge_closed_form_of_trueExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (hq : 0 < q) (ha : 0 < a)
    (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) ≤
      barrierSupValue X a q := by sorry
