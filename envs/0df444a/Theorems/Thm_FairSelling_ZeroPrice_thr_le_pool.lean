-- Prove2me | Theorems.Thm_FairSelling_ZeroPrice_thr_le_pool
-- name    : FairSelling.ZeroPrice.thr_le_pool
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:55:36.139205+00:00
-- url     : https://prove2.me/theorems/33da9ae7-8612-48aa-a41a-1355a536c955
-- title:
--   Zero Price: thr le pool
-- statement:
--   **The counting argument.**  If some agent is unserved, the unallocated goods are worth at
--   least its threshold to it.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L178-L244
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L178-L244

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.ZeroPrice.thr_le_pool (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    {j : Fin n} (hj : j ∉ s.1) :
    thr v p j ≤ bval (v j) (pool s) := by sorry
