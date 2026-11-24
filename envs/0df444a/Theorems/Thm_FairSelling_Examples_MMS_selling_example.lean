-- Prove2me | Theorems.Thm_FairSelling_Examples_MMS_selling_example
-- name    : FairSelling.Examples.MMS_selling_example
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:16:44.286095+00:00
-- url     : https://prove2.me/theorems/77e8e345-b679-4399-99d1-49f08fd89f62
-- title:
--   Examples: MMS selling example
-- statement:
--   With selling, the two-agent maximin share of the single worthless-but-priced good is `1`
--   (sell it and split the proceeds); without selling it would be `0`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L35-L51
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean#L35-L51

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples

theorem FairSelling.Examples.MMS_selling_example : MMS 2 vsell psell = 1 := by sorry
