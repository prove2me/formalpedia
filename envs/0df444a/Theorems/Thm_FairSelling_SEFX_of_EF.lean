-- Prove2me | Theorems.Thm_FairSelling_SEFX_of_EF
-- name    : FairSelling.SEFX_of_EF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:52.501688+00:00
-- url     : https://prove2.me/theorems/369d1c8c-858f-4f6d-a111-af4fd3fef233
-- title:
--   Fair Selling: SEFX of EF
-- statement:
--   `SEFX` is a genuine relaxation of envy-freeness.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L189-L190
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L189-L190

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFX_of_EF (h : EF v p o) : SEFX v p o := by sorry
