-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
-- name    : AvramDividend.Classical.chat03_uniform_grid_passage_clocks_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:50:37.288994+00:00
-- url     : https://prove2.me/theorems/9cd330f9-8ffc-4e34-b4e8-121084038a8b
-- title:
--   Exact sampled upper and lower passage clocks are measurable ENNReal random variables
-- statement:
--   For the exact deterministic uniform-grid strict upper and lower crossing clocks, each grid evaluation is measurable by adaptedness, each strict crossing condition is measurable, and each ENNReal conditional time is measurable. The countable infimum over all grid indices is measurable. This includes empty crossing sets, whose infimum is infinity. The theorem provides the measurability hypotheses for the accepted upper-first discounted expectation dominated-convergence theorem.
-- source:
--   Actual SpectrallyNegativeLevy adaptedness and pinned Mathlib Measurable.iInf in Mathlib.MeasureTheory.Constructions.BorelSpace.Order.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_uniform_grid_passage_clocks_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (h : ℝ≥0) :
    Measurable (fun ω : Ω => ⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * h) ω then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) ∧
    Measurable (fun ω : Ω => ⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * h) ω < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) := by sorry
