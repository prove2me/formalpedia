-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_ge
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:08.063431+00:00
-- url     : https://prove2.me/theorems/28b60a43-a530-46c5-b8c6-111cd825c751
-- title:
--   Timeout Recertification Run: current Rank ge
-- statement:
--   A high/low run cannot finish at a bounded rank once both the switch and
--   terminal ranks are large.  This finite lemma is the rank interface needed to
--   make the final reverse product uniformly positive.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L220-L247
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L220-L247

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_ge
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q Q : ℕ}
    (hHigh : (Q : ℝ) ≤ (P.rHi : ℝ) * (S : ℝ))
    (hLowRatio : (1 / 2 : ℝ) ≤ movingLowRatio K₀ L)
    (hQL : 2 * Q ≤ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    Q ≤ q := by sorry
