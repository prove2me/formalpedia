-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_directFirstPassage
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.directFirstPassage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:17:19.079802+00:00
-- url     : https://prove2.me/theorems/c995d5ed-82a7-5197-9379-501e8e25772d
-- title:
--   Timeout Recertification Run: direct First Passage
-- statement:
--   Every literal timeout run is the direct first passage of the original
--   source through its final threshold.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L266-L286
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L266-L286

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.directFirstPassage
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    IsFirstPassage (2 ^ q) n elapsed := by sorry
