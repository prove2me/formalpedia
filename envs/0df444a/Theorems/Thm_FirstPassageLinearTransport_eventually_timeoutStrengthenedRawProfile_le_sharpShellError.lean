-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutStrengthenedRawProfile_le_sharpShellError
-- name    : FirstPassageLinearTransport.eventually_timeoutStrengthenedRawProfile_le_sharpShellError
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:46:46.172902+00:00
-- url     : https://prove2.me/theorems/fbd7dc08-e4a5-5faa-bfa5-653fbf07248d
-- title:
--   First Passage Linear Transport: eventually timeout Strengthened Raw Profile le sharp Shell Error
-- statement:
--   Scalar closure of the Version 4 ballot profile.  The high failures are
--   absorbed by the fixed polynomial margin; the low timeout term is paid by the
--   sharp critical buffer without a secondary logarithmic debit.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L467-L663
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L467-L663

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutStrengthenedRawProfile_le_sharpShellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A R : ℕ → ℝ} {D : ℝ}
    (hD : 0 < D)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H :=
        (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          (3 * (D / 2) * weightedTailConstant
            firstPassageEndpointRate (firstPassageEndpointRate / 2)) *
          ((1 / Real.sqrt L) *
            Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) +
        4 / R M ≤
      sharpTimeoutEndpointProfileConstant P D *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) +
        4 / R M := by sorry
