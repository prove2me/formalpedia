-- Prove2me | Theorems.Thm_FairSelling_Examples_TPS_example
-- name    : FairSelling.Examples.TPS_example
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:49.990033+00:00
-- url     : https://prove2.me/theorems/33cd754b-10b7-498f-8fbe-1261e869c13f
-- title:
--   Examples: TPS example
-- statement:
--   The truncated proportional share of the instance is `1`, computed through the bracket
--   formula of `TPS_eq_bracket_formula` on the interval `[1, 3]`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L75-L117
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L75-L117

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples

theorem FairSelling.Examples.TPS_example : TPS 2 vex pex = 1 := by sorry
