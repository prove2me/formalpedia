-- Prove2me | Theorems.Thm_FairSelling_MMSEP_le
-- name    : FairSelling.MMSEP_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:53.517817+00:00
-- url     : https://prove2.me/theorems/64641d0a-4e7a-406d-8109-b5163b303797
-- title:
--   Fair Selling: MMSEP le
-- statement:
--   An upper bound on the equal-proceeds MMS is certified by bounding all valid equal-proceeds
--   outcomes.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L87-L89
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L87-L89

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.MMSEP_le (v p : G → ℝ) {c : ℝ} (h : ∀ r ∈ MMSEPset n v p, r ≤ c) :
    MMSEP n v p ≤ c := by sorry
