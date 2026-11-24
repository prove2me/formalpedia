-- Prove2me | Theorems.Thm_FairSelling_lhs_unifiedOutcome
-- name    : FairSelling.lhs_unifiedOutcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:14.342904+00:00
-- url     : https://prove2.me/theorems/d25eab1f-b2a8-48b9-97e3-e646ed36c3e6
-- title:
--   Fair Selling: lhs unified Outcome
-- statement:
--   The left-hand side of the (`ε`-)SEFX conditions for agent `i` in the realization is exactly
--   the conceptual value `v̄_i(A i) + q i` of its bundle.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L94-L100
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L94-L100

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

theorem FairSelling.lhs_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept i) + (unifiedOutcome v p A F q).money i
      = vbarSum (v i) p (A i) + q i := by sorry
