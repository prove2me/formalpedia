-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain
-- name    : FirstPassageLinearTransport.RecertificationRun.toCertifiedRankChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:44.552169+00:00
-- url     : https://prove2.me/theorems/800f35cb-288d-4d8b-a390-294915ac907d
-- title:
--   Recertification Run: to Certified Rank Chain
-- statement:
--   Every literal certified run is an exact certified rank chain.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L66-L94
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L66-L94

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.RecertificationRun.toCertifiedRankChain
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) :
    CertifiedRankChain r n elapsed q := by sorry
