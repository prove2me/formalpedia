-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_exists_TPS_SEFX_of_money_goods
-- name    : FairSelling.GeneralTPS.exists_TPS_SEFX_of_money_goods
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:13.796159+00:00
-- url     : https://prove2.me/theorems/7b63ea96-55f1-4d21-a263-ac650156156c
-- title:
--   General TPS: exists TPS SEFX of money goods
-- statement:
--   **Theorem 2 (SEFX half) for instances whose goods are pure money.**  If no agent values any
--   good above its price, then selling everything and splitting the proceeds equally is a valid
--   outcome that is envy free — hence SEFX — and gives every agent at least `n/(2n−1)` of its
--   truncated proportional share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L423-L454
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L423-L454

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.GeneralTPS.exists_TPS_SEFX_of_money_goods (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hvp : ∀ i g, v i g ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
