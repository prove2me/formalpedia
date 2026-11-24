-- Prove2me | Theorems.Thm_FairSelling_rhs_unifiedOutcome_le
-- name    : FairSelling.rhs_unifiedOutcome_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:26.840151+00:00
-- url     : https://prove2.me/theorems/540ebc70-1a41-4232-9518-02bf6a3e89b3
-- title:
--   Fair Selling: rhs unified Outcome le
-- statement:
--   The bundle that agent `j` keeps, together with the money it receives, is worth to agent `i`
--   at most the conceptual value `v̄_i(A j) + q j` of `j`'s bundle.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L105-L121
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L105-L121

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.rhs_unifiedOutcome_le (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i j : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept j) + (unifiedOutcome v p A F q).money j
      ≤ vbarSum (v i) p (A j) + q j := by sorry
