-- Prove2me | Theorems.Thm_FairChores_cbarSum_univ_le_nsmul_MMS
-- name    : FairChores.cbarSum_univ_le_nsmul_MMS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:52.497882+00:00
-- url     : https://prove2.me/theorems/f265e20b-437d-4c9c-8d6f-de2e9e69897b
-- title:
--   Fair Chores: cbar Sum univ le nsmul MMS
-- statement:
--   Total effective cost is a lower bound for `n` times the maximin share; this is the
--   manuscript's `n · MMSᵢ ≥ c̄ᵢ(M)`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L27-L30
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L27-L30

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
set_option autoImplicit true
open scoped BigOperators
open FairChores

theorem FairChores.cbarSum_univ_le_nsmul_MMS {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) :
    cbarSum c p Finset.univ ≤ n * MMS n c p := by sorry
