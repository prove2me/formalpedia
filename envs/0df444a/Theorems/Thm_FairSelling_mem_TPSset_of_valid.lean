-- Prove2me | Theorems.Thm_FairSelling_mem_TPSset_of_valid
-- name    : FairSelling.mem_TPSset_of_valid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:37:44.113827+00:00
-- url     : https://prove2.me/theorems/6641fac9-f029-4908-b3c1-fbcd13a25aea
-- title:
--   Fair Selling: mem TPSset of valid
-- statement:
--   The Fair Selling construction uses the mem TPSset of valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L298-L322
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L298-L322

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.mem_TPSset_of_valid (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    (o : Outcome G n) (hvalid : o.Valid p) (r : ℝ) (hr : 0 ≤ r)
    (hguar : ∀ j, r ≤ util v o j) :
    r ∈ TPSset n v p := by sorry
