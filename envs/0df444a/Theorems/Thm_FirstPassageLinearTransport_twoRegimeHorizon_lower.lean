-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_twoRegimeHorizon_lower
-- name    : FirstPassageLinearTransport.twoRegimeHorizon_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:21.246846+00:00
-- url     : https://prove2.me/theorems/04802470-3baa-5e3b-9487-c93b866f1d8a
-- title:
--   First Passage Linear Transport: two Regime Horizon lower
-- statement:
--   The real geometric budget lies below its canonical natural ceiling.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L201-L206
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L201-L206

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.twoRegimeHorizon_lower
    (rHi rLo : ℚ) (S M : ℕ) :
    (M : ℝ) / (1 - (rHi : ℝ)) +
        (S : ℝ) / (1 - (rLo : ℝ)) ≤
      (twoRegimeHorizon rHi rLo S M : ℝ) := by sorry
