-- Prove2me | Theorems.Thm_FairSelling_outcomeOf_valid
-- name    : FairSelling.outcomeOf_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:23.411003+00:00
-- url     : https://prove2.me/theorems/baeb4b4b-d871-42bb-8e56-5d0d1f3a4ca9
-- title:
--   Fair Selling: outcome Of valid
-- statement:
--   The outcome `outcomeOf assign m` is feasible provided the money split is nonnegative and
--   does not exceed the available proceeds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L92-L107
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L92-L107

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.outcomeOf_valid (p : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hms : ∑ j, m j ≤ procOf p assign) :
    (outcomeOf assign m).Valid p := by sorry
