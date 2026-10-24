-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_small_negative
-- name    : AvramDividend.Classical.generatorIntegrand_small_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:51:41.037566+00:00
-- url     : https://prove2.me/theorems/2992c4d5-37dc-4dee-88b1-7579f302ae7f
-- title:
--   The Lévy generator compensates jumps in the interval (-1,0)
-- statement:
--   For a small negative Lévy jump, the truncation indicator equals one, so the generator jump integrand contains the exact first-order compensation deriv w x multiplied by y.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generatorIntegrand_small_negative
    (w : ℝ → ℝ) (x y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 0) :
    SpectrallyNegativeLevy.generatorIntegrand w x y =
      w (x + y) - w x - deriv w x * y := by sorry
