-- Prove2me | Theorems.Thm_FairSelling_vbarSum_restrict_subset
-- name    : FairSelling.vbarSum_restrict_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:01.932875+00:00
-- url     : https://prove2.me/theorems/8664261e-c7c8-40a9-a10f-19a2417bba1c
-- title:
--   Fair Selling: vbar Sum restrict subset
-- statement:
--   On a bundle contained in `R`, the restricted `v̄`-value agrees with the unrestricted one.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L256-L260
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L256-L260

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.vbarSum_restrict_subset (w p : G → ℝ) (R B : Finset G) (hB : B ⊆ R) :
    vbarSum (restrictVal R w) (restrictVal R p) B = vbarSum w p B := by sorry
