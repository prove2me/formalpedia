-- Prove2me | Theorems.Thm_FairSelling_exists_MMS_two
-- name    : FairSelling.exists_MMS_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:37:50.335405+00:00
-- url     : https://prove2.me/theorems/32f56203-de62-4170-8dc9-2803ec8bc42f
-- title:
--   Fair Selling: exists MMS two
-- statement:
--   **MMS existence for two agents** (Theorem 1, MMS part). There is a valid outcome giving
--   each of the two agents at least its maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L304-L321
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L304-L321

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_MMS_two (v : Fin 2 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 2, o.Valid p ∧ ∀ i, MMS 2 (v i) p ≤ util (v i) o i := by sorry
