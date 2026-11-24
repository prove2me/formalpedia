-- Prove2me | Theorems.Thm_FairSelling_ZeroPrice_truncBundle_le_two_thr
-- name    : FairSelling.ZeroPrice.truncBundle_le_two_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:38.314865+00:00
-- url     : https://prove2.me/theorems/48d81683-a093-423b-9767-79dabdf8e3bc
-- title:
--   Zero Price: trunc Bundle le two thr
-- statement:
--   **Each safe bundle is worth at most `2τ j` to an unserved agent `j`** (measured through the
--   truncated contributions).  This is the property that keeps the counting argument of Algorithm 4
--   alive.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L118-L174
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L118-L174

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

theorem FairSelling.ZeroPrice.truncBundle_le_two_thr (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    {i : Fin n} (hi : i ∈ s.1) {j : Fin n} (hj : j ∉ s.1) :
    truncBundle (v j) p (TPS n (v j) p) (s.2 i) ≤ 2 * thr v p j := by sorry
