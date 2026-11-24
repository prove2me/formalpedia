-- Prove2me | Theorems.Thm_FairSelling_SEF1_of_EF
-- name    : FairSelling.SEF1_of_EF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:50:46.324929+00:00
-- url     : https://prove2.me/theorems/39d16233-6ff2-4a75-be04-5cfeda5210d4
-- title:
--   Fair Selling: SEF1 of EF
-- statement:
--   `SEF1` is a genuine relaxation of envy-freeness.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L193-L194
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L193-L194

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEF1_of_EF (h : EF v p o) : SEF1 v p o := by sorry
