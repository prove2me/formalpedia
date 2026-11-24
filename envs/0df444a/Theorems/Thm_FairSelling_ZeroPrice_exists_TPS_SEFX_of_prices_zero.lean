-- Prove2me | Theorems.Thm_FairSelling_ZeroPrice_exists_TPS_SEFX_of_prices_zero
-- name    : FairSelling.ZeroPrice.exists_TPS_SEFX_of_prices_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:41:19.042512+00:00
-- url     : https://prove2.me/theorems/679a40cf-7f32-4427-aee8-f67271210fb1
-- title:
--   Zero Price: exists TPS SEFX of prices zero
-- statement:
--   **Theorem 2 (SEFX half) for instances in which no good has a price.**  Every allocation
--   instance with `p ≡ 0` admits a valid outcome that gives every agent at least `n/(2n−1)` of its
--   truncated proportional share and is `SEFX`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L392-L445
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L392-L445

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

theorem FairSelling.ZeroPrice.exists_TPS_SEFX_of_prices_zero (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp0 : ∀ g, p g = 0) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
