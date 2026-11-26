-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_completed_oddCount_centered_le
-- name    : FirstPassageLinearTransport.completed_oddCount_centered_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:26.27987+00:00
-- url     : https://prove2.me/theorems/b50e638b-b62e-55d1-9592-69e395d41017
-- title:
--   First Passage Linear Transport: completed odd Count centered le
-- statement:
--   An exact-halving completion adds no odd shortcut states.  Its centered
--   odd-count error therefore grows by at most half the completion length.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L208-L251
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L208-L251

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.completed_oddCount_centered_le
    {n elapsed q v S : ℕ} {F : ℝ}
    (heq : orbit elapsed n = 2 ^ q)
    (hvq : v ≤ q) (hvS : v ≤ S)
    (hbase : ∀ j : ℕ, j ≤ elapsed →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    ∀ j : ℕ, j ≤ elapsed + v →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F + (S : ℝ) / 2 := by sorry
