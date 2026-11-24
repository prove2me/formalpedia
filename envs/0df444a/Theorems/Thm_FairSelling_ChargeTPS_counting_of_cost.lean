-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_counting_of_cost
-- name    : FairSelling.ChargeTPS.counting_of_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:41:22.838507+00:00
-- url     : https://prove2.me/theorems/5bd6fdb4-16c4-4ce5-a7c8-9da7846dcb45
-- title:
--   Charge TPS: counting of cost
-- statement:
--   **The accounting theorem.**  The local, per-agent cost bound of a good stage implies the
--   counting invariant of Algorithm 4: with `m = n − |served|` agents still unserved, every unserved
--   agent values the pool through its truncated contributions, plus the free bank, at least
--   `(2m − 1)·τ`.
--
--   This is the formal content of the manuscript's remark that `Unshrink` keeps the number of sold
--   goods below the number of served agents.  Nothing is lost in the summation: the identity behind
--   the proof is that the pool plus the bank is exactly `(2n−1)·τ` minus the total cost of the
--   packages handed out.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L179-L257
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L179-L257

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage

theorem FairSelling.ChargeTPS.counting_of_cost (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps) (j : Fin n) (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank := by sorry
