-- Prove2me | Theorems.Thm_FairSelling_vbarSum_kept_unifiedOutcome
-- name    : FairSelling.vbarSum_kept_unifiedOutcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:19.756878+00:00
-- url     : https://prove2.me/theorems/21dcc0b2-fa8f-4bf5-8948-156d47914e8a
-- title:
--   Fair Selling: vbar Sum kept unified Outcome
-- statement:
--   In the realization `unifiedOutcome`, the `v̄`-value of the bundle that agent `i` keeps is the
--   plain `v`-value of that bundle: `i` keeps exactly the goods it values at least as much as their
--   price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L82-L89
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L82-L89

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

theorem FairSelling.vbarSum_kept_unifiedOutcome (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept i)
      = ∑ g ∈ (unifiedOutcome v p A F q).kept i, v i g := by sorry
