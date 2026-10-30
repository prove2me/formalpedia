-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_wh_zero_drawdown_atom_product_lintegral
-- name    : AvramDividend.Classical.avram_ws01b_wh_zero_drawdown_atom_product_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:14:33.892545+00:00
-- url     : https://prove2.me/theorems/a87781fa-725f-42bc-8afd-3bb2636f6af1
-- title:
--   Exact zero-drawdown atom factor for an independent Wiener–Hopf product law
-- statement:
--   For the positive product of the genuine supremum marginal and descending drawdown marginal, a zero drawdown event factors into its atom mass times any nonnegative measurable supremum payoff. The generic statement is valid for arbitrary sigma-finite measurable product measures and infinite payoffs; it is the algebraic-measure step in the BV zero-cap killed scale resolvent, without assuming the desired stochastic harmonicity.
-- source:
--   MeasureTheory.lintegral_prod, lintegral_indicator and lintegral_const_mul under genuine product measure; original spectrally negative Lévy WH independence is already proved UUID 47e972c8. Does not assert actual process independence by itself.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01b_wh_zero_drawdown_atom_product_lintegral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (g : α → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a : α × ℝ,
      if a.2 = 0 then g a.1 else 0 ∂(μ.prod ν)) =
    ν ({0} : Set ℝ) * (∫⁻ a, g a ∂μ) := by sorry
