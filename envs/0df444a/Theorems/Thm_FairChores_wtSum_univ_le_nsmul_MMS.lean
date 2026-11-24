-- Prove2me | Theorems.Thm_FairChores_wtSum_univ_le_nsmul_MMS
-- name    : FairChores.wtSum_univ_le_nsmul_MMS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:30.754332+00:00
-- url     : https://prove2.me/theorems/92c4c0b3-d9bc-4c31-9163-2e776439a1a5
-- title:
--   Fair Chores: wt Sum univ le nsmul MMS
-- statement:
--   **The key bound**: the total weight of all chores, relative to the threshold `MMSᵢ`, is at
--   most `n · MMSᵢ`.  Since `c̄ᵢ ≤ wtᵢ` this refines the manuscript's `c̄ᵢ(M) ≤ n · MMSᵢ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L313-L361
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L313-L361

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}

theorem FairChores.wtSum_univ_le_nsmul_MMS (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) :
    wtSum c p (MMS n c p) Finset.univ ≤ n * MMS n c p := by sorry
