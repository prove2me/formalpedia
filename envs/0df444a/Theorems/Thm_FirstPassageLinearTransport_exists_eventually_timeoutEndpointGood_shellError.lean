-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_eventually_timeoutEndpointGood_shellError
-- name    : FirstPassageLinearTransport.exists_eventually_timeoutEndpointGood_shellError
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:13.857509+00:00
-- url     : https://prove2.me/theorems/0e8de241-c68f-47d0-9830-954ac79a9b29
-- title:
--   First Passage Linear Transport: exists eventually timeout Endpoint Good shell Error
-- statement:
--   The timeout shell family satisfies the same vanishing error profile as
--   the public moving endpoint theorem.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L837-L884
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L837-L884

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_eventually_timeoutEndpointGood_shellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio (timeoutEndpointGood P A M) M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by sorry
