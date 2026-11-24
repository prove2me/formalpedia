-- Prove2me | Theorems.Thm_FairSelling_unifiedOutcome_valid
-- name    : FairSelling.unifiedOutcome_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:11:21.636265+00:00
-- url     : https://prove2.me/theorems/1a2e09b1-babb-4086-b8bd-09ac12a56c30
-- title:
--   Fair Selling: unified Outcome valid
-- statement:
--   Feasibility of `unifiedOutcome`, given that the groups `A i` are pairwise disjoint and
--   disjoint from `F`, the shares are nonnegative, and they do not exceed the force-sale proceeds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L296-L333
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L296-L333

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G]

theorem FairSelling.unifiedOutcome_valid (v : Fin n → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hF : ∀ i, Disjoint F (A i))
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i ≤ ∑ g ∈ F, p g) :
    (unifiedOutcome v p A F q).Valid p := by sorry
