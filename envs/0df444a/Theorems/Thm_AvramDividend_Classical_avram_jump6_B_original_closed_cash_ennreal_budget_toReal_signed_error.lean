-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_closed_cash_ennreal_budget_toReal_signed_error
-- name    : AvramDividend.Classical.avram_jump6_B_original_closed_cash_ennreal_budget_toReal_signed_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:38:30.011815+00:00
-- url     : https://prove2.me/theorems/34d0f540-5ad2-4c2c-994b-bc4755c0357b
-- title:
--   Convert original inclusive ENNReal cash upper budget plus finite mesh error into real budget bound
-- statement:
--   A bounded real signed source estimate is obtained from the original paid cash ENNReal integral upper bound by converting toReal and adding the true nonnegative finite discounted mesh-error term. This is the exact conversion required to combine the source-exact original closed-Iic payment measure upper bound and the fixed canonical physical-grid payment residual, without assuming Cash is finite or clipping its amount.

import Mathlib
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_closed_cash_ennreal_budget_toReal_signed_error
    (Cash Error : ℝ≥0∞) (Budget : ℝ)
    (hBudgetNonneg : 0 ≤ Budget)
    (hErrorFinite : Error ≠ ⊤)
    (hCash : Cash ≤ ENNReal.ofReal Budget + Error) :
    Cash.toReal ≤ Budget + Error.toReal := by sorry
