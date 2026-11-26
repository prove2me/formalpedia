-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_first_of_stage
-- name    : FirstPassageLinearTransport.CertifiedRankChain.first_of_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:16:31.945852+00:00
-- url     : https://prove2.me/theorems/49ebabe9-1ab2-4067-85f8-dd5defe008c1
-- title:
--   Certified Rank Chain: first of stage
-- statement:
--   The first certified stopped-map block initializes the exact rank chain.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L52-L62
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L52-L62

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.CertifiedRankChain.first_of_stage
    {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hr : 0 < r) {m n : ℕ}
    (hm0 : p.M0 ≤ m) (hnShell : n ∈ dyadicShell m)
    (hnGood : n ∈ initialWindowGood eta) :
    CertifiedRankChain r n (stageLength p n) (rationalTargetRank r m) := by sorry
