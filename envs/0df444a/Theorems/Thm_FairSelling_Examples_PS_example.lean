-- Prove2me | Theorems.Thm_FairSelling_Examples_PS_example
-- name    : FairSelling.Examples.PS_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:44.573555+00:00
-- url     : https://prove2.me/theorems/f89e82e9-7fd0-4bed-a479-afb183fe037a
-- title:
--   Examples: PS example
-- statement:
--   The proportional share of the instance is `2`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L69-L71
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L69-L71

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples

theorem FairSelling.Examples.PS_example : PS 2 vex pex = 2 := by sorry
