-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_eventually_timeoutStrengthenedEndpointGood_sharpShellError
-- name    : FirstPassageLinearTransport.exists_eventually_timeoutStrengthenedEndpointGood_sharpShellError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:22.922867+00:00
-- url     : https://prove2.me/theorems/fbd13a20-270b-4de8-a0c2-3c0941bd7ce5
-- title:
--   First Passage Linear Transport: exists eventually timeout Strengthened Endpoint Good sharp Shell Error
-- statement:
--   The strengthened timeout shell family satisfies the sharp Version 4
--   critical-buffer profile, with the common-height exception kept as the literal
--   separate term `4 / R M`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L889-L948
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L889-L948

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_eventually_timeoutStrengthenedEndpointGood_sharpShellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A R : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : ∀ᶠ M : ℕ in atTop, 4 ≤ R M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio
            (timeoutStrengthenedEndpointGood P A R M) M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) +
          4 / R M := by sorry
