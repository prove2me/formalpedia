-- Prove2me | Theorems.Thm_FairSelling_Examples_MMS_example
-- name    : FairSelling.Examples.MMS_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:55.513667+00:00
-- url     : https://prove2.me/theorems/0c1f91bc-c38c-4e79-b539-40004e0f22b7
-- title:
--   Examples: MMS example
-- statement:
--   The maximin share with selling of the instance is `1`: it equals the `TPS` here, and both
--   are strictly below the proportional share `2`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L121-L135
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L121-L135

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples

theorem FairSelling.Examples.MMS_example : MMS 2 vex pex = 1 := by sorry
