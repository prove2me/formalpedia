-- Prove2me | Theorems.Thm_FairSelling_exists_outcome_ge_MMS
-- name    : FairSelling.exists_outcome_ge_MMS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:29:01.182451+00:00
-- url     : https://prove2.me/theorems/0a4d631c-dbbc-40a2-b9e5-1454226e54bf
-- title:
--   Fair Selling: exists outcome ge MMS
-- statement:
--   There is a valid outcome giving every agent (part) at least its maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L231-L233
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L231-L233

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.exists_outcome_ge_MMS (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ j, MMS n v p ≤ util v o j := by sorry
