-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
-- name    : FirstPassageLinearTransport.CertifiedRankChain.directFirstPassage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:55.822191+00:00
-- url     : https://prove2.me/theorems/08336e98-c16b-4dba-bfc6-07899a49de46
-- title:
--   Certified Rank Chain: direct First Passage
-- statement:
--   Every cumulative landing of a certified rank chain is a direct first
--   passage of the original source.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L141-L149
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L141-L149

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.CertifiedRankChain.directFirstPassage
    {r : ℚ} {n t q : ℕ} (hchain : CertifiedRankChain r n t q) :
    IsFirstPassage (2 ^ q) n t := by sorry
