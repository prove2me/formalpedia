-- Prove2me | Theorems.Thm_FairSelling_kept_eq_of_money_zero
-- name    : FairSelling.kept_eq_of_money_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:22.751204+00:00
-- url     : https://prove2.me/theorems/edf7866b-d455-4b6b-982f-f411b48c152b
-- title:
--   Fair Selling: kept eq of money zero
-- statement:
--   If the money handed to agent `j` in the realization is `0`, then `j` sells nothing and keeps
--   its whole bundle.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L126-L152
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L126-L152

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

theorem FairSelling.kept_eq_of_money_zero (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (j : Fin n) (hmoney : (unifiedOutcome v p A F q).money j = 0) :
    (unifiedOutcome v p A F q).kept j = A j ∧ q j = 0 := by sorry
