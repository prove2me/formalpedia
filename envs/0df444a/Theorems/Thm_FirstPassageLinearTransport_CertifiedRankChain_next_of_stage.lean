-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_next_of_stage
-- name    : FirstPassageLinearTransport.CertifiedRankChain.next_of_stage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:16.589401+00:00
-- url     : https://prove2.me/theorems/800aa157-b15c-4eed-bb77-8e7895fcaf20
-- title:
--   Certified Rank Chain: next of stage
-- statement:
--   One further certified stopped-map block extends an existing exact rank
--   chain once its target rank is strictly lower.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L66-L80
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L66-L80

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.CertifiedRankChain.next_of_stage
    {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hr : 0 < r) {n elapsed qprev m : ℕ}
    (hchain : CertifiedRankChain r n elapsed qprev)
    (hm0 : p.M0 ≤ m) (hsourceShell : orbit elapsed n ∈ dyadicShell m)
    (hsourceGood : orbit elapsed n ∈ initialWindowGood eta)
    (hgap : rationalTargetRank r m < qprev) :
    CertifiedRankChain r n
      (elapsed + stageLength p (orbit elapsed n))
      (rationalTargetRank r m) := by sorry
