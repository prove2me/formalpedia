-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingPolylogTerminalProfile_le_power
-- name    : FirstPassageLinearTransport.eventually_shrinkingPolylogTerminalProfile_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:41.650782+00:00
-- url     : https://prove2.me/theorems/838ee6a8-47c6-4632-ab44-f629ccd14398
-- title:
--   First Passage Linear Transport: eventually shrinking Polylog Terminal Profile le power
-- statement:
--   Scalar closure of the support-sensitive master profile.  The high-rank
--   term spends `5/2` powers because it carries the quadratic rank multiplier;
--   the low terminal tail spends only `1/2` through the feasible-time support.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L214-L320
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L214-L320

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_shrinkingPolylogTerminalProfile_le_power
    (P : ShrinkingBarrierRunData)
    {A C b b' c' kappa : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (hHigh : kappa <
      min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2) - 5 / 2)
    (hLow : kappa < A * min b' c' / Real.log 2 - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      let dHi := shrinkingHighDensityProfile P C M
      let H := (shrinkingTimeSupportConstant P C + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      dHi + H * (1 + 6 / (P.rStar : ℝ)) *
          (((M : ℝ) + 1) ^ 2 * dHi +
            terminalTailBound b b' c' (polylogTerminalRank A M)) ≤
        shrinkingPolylogProfileConstant P C b b' c' *
          (((M : ℝ) + 2) ^ (-kappa)) := by sorry
