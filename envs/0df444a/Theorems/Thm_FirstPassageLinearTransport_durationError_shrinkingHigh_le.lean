-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_durationError_shrinkingHigh_le
-- name    : FirstPassageLinearTransport.durationError_shrinkingHigh_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:18.827037+00:00
-- url     : https://prove2.me/theorems/4a16fa75-2d2e-4e4e-b6fc-59f90f200854
-- title:
--   First Passage Linear Transport: duration Error shrinking High le
-- statement:
--   The high-rank width is at most a square-root rank cost.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L53-L112
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L53-L112

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.durationError_shrinkingHigh_le
    (P : ShrinkingBarrierRunData) {M m : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) :
    durationError (shrinkingHighTolerance P M m) m ≤
      (P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by sorry
