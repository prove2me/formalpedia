-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageRawClock_le
-- name    : FirstPassageLinearTransport.stageRawClock_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:28.148106+00:00
-- url     : https://prove2.me/theorems/a875c511-a272-4365-a6e5-2420faf00c80
-- title:
--   First Passage Linear Transport: stage Raw Clock le
-- statement:
--   Exact fixed-depth raw-time estimate obtained by combining the shortcut
--   clock with the generated odd-count bound.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L175-L226
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L175-L226

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stageRawClock_le
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (rawTime n (stageClock p R n) : ℝ) ≤
      clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
        (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) := by sorry
