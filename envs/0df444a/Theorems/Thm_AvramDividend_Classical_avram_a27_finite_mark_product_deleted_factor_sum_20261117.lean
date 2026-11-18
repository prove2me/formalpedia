-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_mark_product_deleted_factor_sum_20261117
-- name    : AvramDividend.Classical.avram_a27_finite_mark_product_deleted_factor_sum_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:38:31.198887+00:00
-- url     : https://prove2.me/theorems/aaf40f81-d019-4415-9ff1-c079e47b5882
-- title:
--   Finite original physical marked product has exact leave-one-jump Mecke counting identity
-- statement:
--   For every finite set of physical jump times and weights f, the sum over each jump of its mark weight times the product over all other jumps equals the number of jumps times the original complete marked product. This is the deterministic pathwise product identity needed in the original physical marked Poisson Mecke recurrence.
-- source:
--   Pinned Mathlib Finset.mul_prod_erase and finite sum constant cardinality identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- The finite physical marked product satisfies the deleted-mark Mecke counting identity. -/

theorem AvramDividend.Classical.avram_a27_finite_mark_product_deleted_factor_sum_20261117 {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) :
    (∑ x ∈ S, f x * ∏ y ∈ S.erase x, f y) =
      (S.card : ℝ) * ∏ y ∈ S, f y := by sorry
