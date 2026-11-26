-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_centered_of_reverseProduct_half
-- name    : FirstPassageLinearTransport.oddCount_centered_of_reverseProduct_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:00.789651+00:00
-- url     : https://prove2.me/theorems/3eace331-0634-4515-bb60-2b4ffb57c3be
-- title:
--   First Passage Linear Transport: odd Count centered of reverse Product half
-- statement:
--   The exact reverse identity converts a prefix lower bound for the reverse
--   product and a shortcut logarithmic tube into a centered odd-count tube.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L714-L768
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L714-L768

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.oddCount_centered_of_reverseProduct_half
    {n j : ℕ} {E : ℝ}
    (hn : 0 < n)
    (hP : (1 / 2 : ℚ) ≤ reverseProduct n j)
    (hdev : |shortcutLogDeviation n j| ≤ E) :
    |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
      (E + Real.log 2) / Real.log 3 := by sorry
