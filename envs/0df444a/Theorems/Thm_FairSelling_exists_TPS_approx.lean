-- Prove2me | Theorems.Thm_FairSelling_exists_TPS_approx
-- name    : FairSelling.exists_TPS_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:43.702254+00:00
-- url     : https://prove2.me/theorems/95d8ece9-203b-4f20-aef2-3d2ed7cf5ce2
-- title:
--   Fair Selling: exists TPS approx
-- statement:
--   **Theorem 2 of the manuscript (the TPS half).**  Every allocation instance with optional
--   selling admits a valid outcome giving every agent at least `n/(2n−1)` of its truncated
--   proportional share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L367-L410
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L367-L410

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_TPS_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      ∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i := by sorry
