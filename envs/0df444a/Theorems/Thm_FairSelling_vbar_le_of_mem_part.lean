-- Prove2me | Theorems.Thm_FairSelling_vbar_le_of_mem_part
-- name    : FairSelling.vbar_le_of_mem_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:41.811264+00:00
-- url     : https://prove2.me/theorems/f7bc77b2-9d61-45eb-bda8-d9fd056edd2d
-- title:
--   Fair Selling: vbar le of mem part
-- statement:
--   Every good of a part is worth at most `μ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L105-L114
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L105-L114

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
omit [Fintype G] [DecidableEq G]

theorem FairSelling.vbar_le_of_mem_part (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    {j : Fin k} {g : G} (hg : g ∈ E.part j) : vbar w p g ≤ μ := by sorry
