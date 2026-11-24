-- Prove2me | Theorems.Thm_FairSelling_SEF1_of_SEFX
-- name    : FairSelling.SEF1_of_SEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:50:56.990823+00:00
-- url     : https://prove2.me/theorems/646f62b3-48ee-4b8d-a26c-41e112365d4b
-- title:
--   Fair Selling: SEF1 of SEFX
-- statement:
--   `SEFX` implies `SEF1` (for a valid outcome and non-negative valuations: these are needed
--   only to handle an empty envied bundle).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L204-L217
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L204-L217

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEF1_of_SEFX (hv : ∀ i g, 0 ≤ v i g) (hvalid : o.Valid p) (h : SEFX v p o) :
    SEF1 v p o := by sorry
