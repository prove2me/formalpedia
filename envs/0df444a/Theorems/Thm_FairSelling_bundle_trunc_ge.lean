-- Prove2me | Theorems.Thm_FairSelling_bundle_trunc_ge
-- name    : FairSelling.bundle_trunc_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:51:01.723811+00:00
-- url     : https://prove2.me/theorems/a436bc4f-db2c-459c-b36a-5c9d713da4f7
-- title:
--   Fair Selling: bundle trunc ge
-- statement:
--   The Fair Selling construction uses the bundle trunc ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L286-L292
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L286-L292

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.bundle_trunc_ge (v : G → ℝ) (hv : ∀ g, 0 ≤ v g) (o : Outcome G n)
    (j : Fin n) (r : ℝ) (hr : 0 ≤ r) (hmj : 0 ≤ o.money j) (hj : r ≤ util v o j) :
    r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j := by sorry
