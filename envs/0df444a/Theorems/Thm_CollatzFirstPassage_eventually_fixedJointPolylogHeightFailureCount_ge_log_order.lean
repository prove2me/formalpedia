-- Prove2me | Theorems.Thm_CollatzFirstPassage_eventually_fixedJointPolylogHeightFailureCount_ge_log_order
-- name    : CollatzFirstPassage.eventually_fixedJointPolylogHeightFailureCount_ge_log_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:16.561031+00:00
-- url     : https://prove2.me/theorems/09efbd9e-700d-5ef5-83fe-fda4e37c9a49
-- title:
--   Collatz First Passage: eventually fixed Joint Polylog Height Failure Count ge log order
-- statement:
--   The Collatz First Passage construction uses the eventually fixed Joint Polylog Height Failure Count ge log order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean#L259-L280
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean#L259-L280

import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Definitions.Def_FirstPassageLinearTransport_Solution
import Theorems.Thm_FirstPassageLinearTransport_eventually_fixedJointPolylogHeightFailureCount_ge_log_order

set_option autoImplicit true
open CollatzFirstPassage
open Filter
open scoped BigOperators Real Topology

theorem CollatzFirstPassage.eventually_fixedJointPolylogHeightFailureCount_ge_log_order
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by sorry
