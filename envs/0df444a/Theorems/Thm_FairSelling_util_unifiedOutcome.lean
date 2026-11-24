-- Prove2me | Theorems.Thm_FairSelling_util_unifiedOutcome
-- name    : FairSelling.util_unifiedOutcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:11:34.994045+00:00
-- url     : https://prove2.me/theorems/7055e298-44cd-4d3f-bfda-cd688a185c58
-- title:
--   Fair Selling: util unified Outcome
-- statement:
--   Under `unifiedOutcome`, agent `i` obtains exactly `v̄i (A i) + q i`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L274-L291
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L274-L291

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G]

theorem FairSelling.util_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    util (v i) (unifiedOutcome v p A F q) i = vbarSum (v i) p (A i) + q i := by sorry
