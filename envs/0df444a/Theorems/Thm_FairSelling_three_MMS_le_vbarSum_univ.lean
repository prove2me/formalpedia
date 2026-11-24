-- Prove2me | Theorems.Thm_FairSelling_three_MMS_le_vbarSum_univ
-- name    : FairSelling.three_MMS_le_vbarSum_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:23.22205+00:00
-- url     : https://prove2.me/theorems/c20d5812-1d18-4419-a1c6-300dbd9ca29f
-- title:
--   Fair Selling: three MMS le vbar Sum univ
-- statement:
--   **Total `v̄`-value bound.**  For three agents, the total `v̄`-value of all goods is at least
--   `3 · MMS`.  (Any maximin partition splits the goods into three parts of value `≥ MMS`, and the
--   sum of the parts' values never exceeds the total `v̄`-value.)
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L296-L331
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L296-L331

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.three_MMS_le_vbarSum_univ (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    3 * MMS 3 w p ≤ vbarSum w p Finset.univ := by sorry
