-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_eventually_timeoutEndpointGood_rawProfile
-- name    : FirstPassageLinearTransport.exists_eventually_timeoutEndpointGood_rawProfile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:46:35.475013+00:00
-- url     : https://prove2.me/theorems/e573c616-b489-4baa-9c64-8f18d5573fb2
-- title:
--   First Passage Linear Transport: exists eventually timeout Endpoint Good raw Profile
-- statement:
--   Literal timeout shell profile before its last scalar simplification.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L39-L238
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L39-L238

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_eventually_timeoutEndpointGood_rawProfile
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio (timeoutEndpointGood P A M) M ≤
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
              (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by sorry
