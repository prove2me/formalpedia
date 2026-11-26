-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutEndpointRawProfile_le_shellError
-- name    : FirstPassageLinearTransport.eventually_timeoutEndpointRawProfile_le_shellError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:10.455369+00:00
-- url     : https://prove2.me/theorems/3888bc7c-db69-4558-ba08-f7080746960d
-- title:
--   First Passage Linear Transport: eventually timeout Endpoint Raw Profile le shell Error
-- statement:
--   Scalar closure of the sharp timeout profile.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L666-L833
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L666-L833

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutEndpointRawProfile_le_shellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H :=
        (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      let b := firstPassageEndpointRate - D / (L : ℝ)
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant
            (firstPassageEndpointRate / 2) (C / 2) *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) ≤
        timeoutEndpointProfileConstant P C D *
          ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by sorry
