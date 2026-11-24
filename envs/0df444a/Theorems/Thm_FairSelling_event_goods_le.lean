-- Prove2me | Theorems.Thm_FairSelling_event_goods_le
-- name    : FairSelling.event_goods_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:38.606232+00:00
-- url     : https://prove2.me/theorems/130f8aaf-d22c-4f97-bb78-36d0cc94dfd5
-- title:
--   Fair Selling: event goods le
-- statement:
--   The `v̄`-value that the parts and the sell set of an equi-valued partition see inside a set
--   `A` of goods is at most the total `v̄`-value of `A`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L119-L139
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L119-L139

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G]

theorem FairSelling.event_goods_le (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g) (A : Finset G) :
    (∑ j, vbarSum w p (E.part j ∩ A)) + (∑ g ∈ E.sell ∩ A, p g) ≤ ∑ g ∈ A, vbar w p g := by sorry
