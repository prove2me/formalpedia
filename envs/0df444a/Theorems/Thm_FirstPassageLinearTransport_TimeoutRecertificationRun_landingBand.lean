-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_landingBand
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.landingBand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:21:18.849797+00:00
-- url     : https://prove2.me/theorems/5113ef0c-a8ca-4954-96f1-a115b8dfd130
-- title:
--   Timeout Recertification Run: landing Band
-- statement:
--   Every reached endpoint lies in the first-passage landing band.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L289-L293
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L289-L293

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.landingBand
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    2 ^ q < 2 * orbit elapsed n ∧ orbit elapsed n ≤ 2 ^ q := by sorry
