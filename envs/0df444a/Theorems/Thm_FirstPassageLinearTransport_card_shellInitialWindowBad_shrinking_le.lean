-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_shrinking_le
-- name    : FirstPassageLinearTransport.card_shellInitialWindowBad_shrinking_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:11.760547+00:00
-- url     : https://prove2.me/theorems/3816802c-8067-568a-9c40-51a18da18c33
-- title:
--   First Passage Linear Transport: card shell Initial Window Bad shrinking le
-- statement:
--   Outer-shell density bound for the initial shrinking certification.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L77-L113
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L77-L113

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_shellInitialWindowBad_shrinking_le
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M ≤ M) :
    ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
          Real.log ((M : ℝ) + 2))) := by sorry
