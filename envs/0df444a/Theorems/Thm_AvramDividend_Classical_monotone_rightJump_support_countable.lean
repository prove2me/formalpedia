-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_rightJump_support_countable
-- name    : AvramDividend.Classical.monotone_rightJump_support_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:08:22.024953+00:00
-- url     : https://prove2.me/theorems/cffe66ed-fbb7-4567-b821-9a2f310c7a5f
-- title:
--   The set of nonzero right jumps of a monotone real path is countable
-- statement:
--   Every monotone real-valued path has at most countably many times where the right limit differs from its current value. Such times are points of discontinuity, and Mathlib Monotone.countable_not_continuousAt proves that the discontinuity set is countable. This identifies the full atomic support for the dividend Stieltjes measure.
-- source:
--   Pinned Mathlib Monotone.countable_not_continuousAt and ContinuousWithinAt.rightLim_eq.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.monotone_rightJump_support_countable
    (f : ℝ → ℝ) (hf : Monotone f) :
    Set.Countable {t : ℝ | Function.rightLim f t ≠ f t} := by sorry
