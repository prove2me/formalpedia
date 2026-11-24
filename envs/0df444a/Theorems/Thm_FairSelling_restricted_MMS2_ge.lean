-- Prove2me | Theorems.Thm_FairSelling_restricted_MMS2_ge
-- name    : FairSelling.restricted_MMS2_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:31:02.07636+00:00
-- url     : https://prove2.me/theorems/c8cb7922-8e54-4c32-9930-05c06fdfe4d7
-- title:
--   Fair Selling: restricted MMS2 ge
-- statement:
--   **Restricted two-agent MMS lower bound.**  If the goods `R` can be split into two disjoint
--   sub-bundles `B1, B2 ⊆ R`, each of `v̄`-value at least `r`, then the two-agent maximin share of
--   the restricted instance is at least `r`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L265-L291
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L265-L291

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.restricted_MMS2_ge (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R B1 B2 : Finset G) (r : ℝ)
    (hdisj : Disjoint B1 B2) (hB1 : B1 ⊆ R) (hB2 : B2 ⊆ R)
    (h1 : r ≤ vbarSum w p B1) (h2 : r ≤ vbarSum w p B2) :
    r ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by sorry
