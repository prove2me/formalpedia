-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutStrengthenedFailureEnvelope_card_le
-- name    : FirstPassageLinearTransport.timeoutStrengthenedFailureEnvelope_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:46:14.339732+00:00
-- url     : https://prove2.me/theorems/03335faa-aaa8-506a-aa2f-dd07d5064ed1
-- title:
--   First Passage Linear Transport: timeout Strengthened Failure Envelope card le
-- statement:
--   The First Passage Linear Transport construction uses the timeout Strengthened Failure Envelope card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L290-L296
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L290-L296

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutStrengthenedFailureEnvelope_card_le
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (M L S : ℕ) (R : ℝ) :
    (timeoutStrengthenedFailureEnvelope P K₀ M L S R).card ≤
      (timeoutSeparatedFailureEnvelope P K₀ M L S).card +
        (shellMultiplicativeHit M (R / 4)).card := by sorry
