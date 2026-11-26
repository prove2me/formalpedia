-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_scaledReverseLoss_rank_step
-- name    : FirstPassageLinearTransport.scaledReverseLoss_rank_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:48.668909+00:00
-- url     : https://prove2.me/theorems/5abbaeef-468f-431c-b7cb-643534788822
-- title:
--   First Passage Linear Transport: scaled Reverse Loss rank step
-- statement:
--   Applied form of the numerical step for two concatenated first-passage
--   segments.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L86-L121
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L86-L121

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.scaledReverseLoss_rank_step
    {q d m n k h : ℕ} {r : ℚ}
    (hr : 0 < r)
    (hprevious :
      scaledReverseLoss (2 ^ (q + d + 1)) n k ≤
        ((q + d + 3 : ℕ) : ℚ) / r)
    (hlocalFP : IsFirstPassage (2 ^ q) (orbit k n) h)
    (hhm : h ≤ m)
    (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
    scaledReverseLoss (2 ^ q) n (k + h) ≤
      ((q + 2 : ℕ) : ℚ) / r := by sorry
