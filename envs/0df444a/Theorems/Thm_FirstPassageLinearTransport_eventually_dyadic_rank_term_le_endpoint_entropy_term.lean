-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_dyadic_rank_term_le_endpoint_entropy_term
-- name    : FirstPassageLinearTransport.eventually_dyadic_rank_term_le_endpoint_entropy_term
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:57.109531+00:00
-- url     : https://prove2.me/theorems/07ccd4c4-00b4-5724-b047-3392a883ef8d
-- title:
--   First Passage Linear Transport: eventually dyadic rank term le endpoint entropy term
-- statement:
--   The endpoint entropy term eventually dominates the faster dyadic term.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean#L28-L92
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean#L28-L92

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_dyadic_rank_term_le_endpoint_entropy_term :
    ∀ᶠ L : ℕ in atTop,
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L *
          Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by sorry
