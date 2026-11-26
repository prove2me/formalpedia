-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_scaledReverseLoss_le
-- name    : FirstPassageLinearTransport.CertifiedRankChain.scaledReverseLoss_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:12:19.165075+00:00
-- url     : https://prove2.me/theorems/ac1fc324-2cf0-520a-9075-efbad347afee
-- title:
--   Certified Rank Chain: scaled Reverse Loss le
-- statement:
--   The complete all-block rank-scaled loss estimate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L152-L184
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L152-L184

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.CertifiedRankChain.scaledReverseLoss_le
    {r : ℚ} (hr : 0 < r) {n t q : ℕ}
    (hchain : CertifiedRankChain r n t q) :
    scaledReverseLoss (2 ^ q) n t ≤ ((q + 2 : ℕ) : ℚ) / r := by sorry
