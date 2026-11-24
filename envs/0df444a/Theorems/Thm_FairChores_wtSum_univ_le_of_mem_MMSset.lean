-- Prove2me | Theorems.Thm_FairChores_wtSum_univ_le_of_mem_MMSset
-- name    : FairChores.wtSum_univ_le_of_mem_MMSset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:54.282619+00:00
-- url     : https://prove2.me/theorems/69b8ebbf-2dca-4a68-9d3f-ba0a32429d5f
-- title:
--   Fair Chores: wt Sum univ le of mem MMSset
-- statement:
--   If no chore has effective cost in the interval `(mu, r]` and some feasible outcome costs
--   every agent at most `r`, then the total weight of all chores is at most `n · r`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L276-L309
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L276-L309

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}

theorem FairChores.wtSum_univ_le_of_mem_MMSset (hc : ∀ t, 0 ≤ c t) {r : ℝ}
    (hgap : ∀ t, mu < cbar c p t → r < cbar c p t) (hr : r ∈ MMSset n c p) :
    wtSum c p mu Finset.univ ≤ n * r := by sorry
