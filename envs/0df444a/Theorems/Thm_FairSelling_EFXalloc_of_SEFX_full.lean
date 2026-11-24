-- Prove2me | Theorems.Thm_FairSelling_EFXalloc_of_SEFX_full
-- name    : FairSelling.EFXalloc_of_SEFX_full
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:22.704716+00:00
-- url     : https://prove2.me/theorems/4f861cd9-de8a-401d-a191-841f75f8de53
-- title:
--   Fair Selling: EFXalloc of SEFX full
-- statement:
--   If no good is sellable (so that all prices vanish), a full `SEFX` allocation *is* an `EFX`
--   allocation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L111-L143
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L111-L143

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.EFXalloc_of_SEFX_full (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (p : G → ℝ)
    (hp : ∀ g, p g = 0) (o : Outcome G n) (hfull : o.Full p ∅) (hsefx : SEFX v p o) :
    IsPartitionOf o.kept Finset.univ ∧ EFXalloc v o.kept := by sorry
