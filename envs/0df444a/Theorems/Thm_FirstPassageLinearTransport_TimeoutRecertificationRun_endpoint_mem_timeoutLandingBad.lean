-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_endpoint_mem_timeoutLandingBad
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_mem_timeoutLandingBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:12.13893+00:00
-- url     : https://prove2.me/theorems/22a37cc7-f643-4549-9d32-ba57bf3e7d88
-- title:
--   Timeout Recertification Run: endpoint mem timeout Landing Bad
-- statement:
--   A timeout run endpoint at rank `p` that times out in its own shell lies
--   in the literal timeout landing target.  The dyadic upper endpoint is excluded
--   by its exact halving orbit.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L35-L62
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L35-L62

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_mem_timeoutLandingBad
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed p : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed p)
    (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (htimeout : LowStageTimeout K₀ L (p - 1) (orbit elapsed n)) :
    orbit elapsed n ∈ timeoutLandingBad K₀ L p := by sorry
