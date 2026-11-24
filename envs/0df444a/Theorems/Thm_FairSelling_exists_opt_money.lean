-- Prove2me | Theorems.Thm_FairSelling_exists_opt_money
-- name    : FairSelling.exists_opt_money
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:25.613311+00:00
-- url     : https://prove2.me/theorems/453ef7bf-6200-49fa-b77b-e78a61d1730a
-- title:
--   Fair Selling: exists opt money
-- statement:
--   For a fixed assignment, the money split maximising the worst-bundle utility exists
--   (compactness of the money simplex).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L112-L138
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L112-L138

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.exists_opt_money (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (assign : G → Option (Fin n)) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (∑ j, m j ≤ procOf p assign) ∧
      ∀ m', (∀ j, 0 ≤ m' j) → (∑ j, m' j ≤ procOf p assign) →
        minUtilData v assign m' ≤ minUtilData v assign m := by sorry
