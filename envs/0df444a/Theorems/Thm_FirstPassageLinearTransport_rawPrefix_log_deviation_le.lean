-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawPrefix_log_deviation_le
-- name    : FirstPassageLinearTransport.rawPrefix_log_deviation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:25.093539+00:00
-- url     : https://prove2.me/theorems/77cb4d63-b39f-5b8b-b978-1a560d64ea8f
-- title:
--   First Passage Linear Transport: raw Prefix log deviation le
-- statement:
--   Uniform shortcut and odd-count tubes control every raw prefix; the final
--   `log 2` pays the unique intermediate odd image.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L167-L204
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L167-L204

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawPrefix_log_deviation_le
    {n k : ℕ} {E F : ℝ}
    (hn : 0 < n)
    (hshortcut : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E)
    (hodd : ∀ j : ℕ, j ≤ k →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    ∀ i : ℕ, i ≤ rawTime n k →
      |rawLogDeviation n i| ≤
        E + rawOddDeviationCoefficient * F + Real.log 2 := by sorry
