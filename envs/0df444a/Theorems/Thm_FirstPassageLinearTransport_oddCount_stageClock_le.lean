-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_stageClock_le
-- name    : FirstPassageLinearTransport.oddCount_stageClock_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:23.146163+00:00
-- url     : https://prove2.me/theorems/d71499c9-69e1-5c94-a7e4-595f1102b910
-- title:
--   First Passage Linear Transport: odd Count stage Clock le
-- statement:
--   Odd counts across a fixed stopped bootstrap obey the same finite
--   geometric logarithmic profile as the shortcut clock.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L71-L167
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L71-L167

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.oddCount_stageClock_le
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (oddCount n (stageClock p R n) : ℝ) ≤
      (stageClock p R n : ℝ) / 2 +
        eta / Real.log 3 *
          (clockGeom r R * Real.log n +
            (R : ℝ) ^ 2 * Real.log (stageK p)) := by sorry
