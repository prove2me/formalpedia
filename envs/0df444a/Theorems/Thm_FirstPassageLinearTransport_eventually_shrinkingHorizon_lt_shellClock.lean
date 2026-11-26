-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingHorizon_lt_shellClock
-- name    : FirstPassageLinearTransport.eventually_shrinkingHorizon_lt_shellClock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:04.473449+00:00
-- url     : https://prove2.me/theorems/e6c71c97-3199-465f-ba50-6a43c47083db
-- title:
--   First Passage Linear Transport: eventually shrinking Horizon lt shell Clock
-- statement:
--   The linear-log switch contributes only a lower-order term to the
--   two-regime clock.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L371-L455
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L371-L455

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_shrinkingHorizon_lt_shellClock
    {rHi rLo : ℚ} {C c : ℝ}
    (hrHi1 : rHi < 1) (hrLo1 : rLo < 1)
    (hC : 0 ≤ C)
    (hlead : 1 / (1 - (rHi : ℝ)) < c * Real.log 2) :
    ∀ᶠ M : ℕ in atTop,
      (twoRegimeHorizon rHi rLo (shrinkingSwitchRank C M) M : ℝ) <
        c * (M : ℝ) * Real.log 2 := by sorry
