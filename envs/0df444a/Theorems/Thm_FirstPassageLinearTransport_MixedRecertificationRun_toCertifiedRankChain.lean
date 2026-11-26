-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_MixedRecertificationRun_toCertifiedRankChain
-- name    : FirstPassageLinearTransport.MixedRecertificationRun.toCertifiedRankChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:03.554894+00:00
-- url     : https://prove2.me/theorems/5af3e42b-373d-58b7-994e-edd2af3a4c91
-- title:
--   Mixed Recertification Run: to Certified Rank Chain
-- statement:
--   Every variable-regime run is one exact rank chain for `rStar`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeRun.lean#L102-L112
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeRun.lean#L102-L112

import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.MixedRecertificationRun.toCertifiedRankChain
    {rStar : ℚ} (hrStar : 0 < rStar) {n elapsed q : ℕ}
    (hrun : MixedRecertificationRun rStar n elapsed q) :
    CertifiedRankChain rStar n elapsed q := by sorry
