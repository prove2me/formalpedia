-- Prove2me | Theorems.Thm_FairSelling_PotTPS_exists_TPS_SEFX_of_Qstep
-- name    : FairSelling.PotTPS.exists_TPS_SEFX_of_Qstep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:28.585074+00:00
-- url     : https://prove2.me/theorems/8572f8d2-3cce-44f2-9554-59686b977bba
-- title:
--   Pot TPS: exists TPS SEFX of Qstep
-- statement:
--   **Theorem 2 (SEFX half) reduces to the ledger improvement step.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L631-L661
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L631-L661

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.PotTPS.exists_TPS_SEFX_of_Qstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → QImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
