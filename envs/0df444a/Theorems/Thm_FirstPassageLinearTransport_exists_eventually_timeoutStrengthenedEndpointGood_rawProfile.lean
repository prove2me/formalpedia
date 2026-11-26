-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_eventually_timeoutStrengthenedEndpointGood_rawProfile
-- name    : FirstPassageLinearTransport.exists_eventually_timeoutStrengthenedEndpointGood_rawProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:04.455719+00:00
-- url     : https://prove2.me/theorems/50f632ac-f38d-40be-9207-8e3e12c4f066
-- title:
--   First Passage Linear Transport: exists eventually timeout Strengthened Endpoint Good raw Profile
-- statement:
--   Version 4 shell profile.  The finite ballot timeout is used at the exact
--   endpoint rate, the former secondary logarithmic debit is absent, and the
--   initial multiplicative-maximum exception contributes the separate term
--   `4 / R M`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L244-L443
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L244-L443

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_eventually_timeoutStrengthenedEndpointGood_rawProfile
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A R : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : ∀ᶠ M : ℕ in atTop, 4 ≤ R M) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio (timeoutStrengthenedEndpointGood P A R M) M ≤
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
            4 / R M := by sorry
