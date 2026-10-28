-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_actual_grid
-- name    : AvramDividend.Classical.barrierSupValue_ge_left_scale_quotient_of_actual_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:26:03.169557+00:00
-- url     : https://prove2.me/theorems/5cc63fb8-c1ce-444a-86f5-9f6f1606d6fc
-- title:
--   Actual killed-record grid bounds imply the left scale quotient
-- statement:
--   Any geometric lower bounds on actual killed first-record discounted weights give the scale-quotient lower bound on the reflected dividend value. The pathwise stopped Stieltjes budget and ae measurability of the grid weights have already been proved.
-- source:
--   Proved stopped_firstRecord_grid_pathwise_budget (e4632c68-2cd1-4584-b08e-62e3089f7b66), chat08_record_grid_stopped_weights_aemeasurable (5d88c767-9308-4e95-818f-3e7dc2e6c8ba), and barrierSupValue_ge_left_scale_quotient_of_record_budgets (88d484b2-cd02-4fc7-986b-d564b206c1c5).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_record_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.barrierSupValue_ge_left_scale_quotient_of_actual_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (a q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hgrid : ∀ n : ℕ,
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
        (∫⁻ ω,
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :
    ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
      barrierSupValue X a q := by sorry
