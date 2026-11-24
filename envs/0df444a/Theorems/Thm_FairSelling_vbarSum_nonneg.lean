-- Prove2me | Theorems.Thm_FairSelling_vbarSum_nonneg
-- name    : FairSelling.vbarSum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:19.515002+00:00
-- url     : https://prove2.me/theorems/ee03d7d7-38aa-4db5-9d33-330948011b1c
-- title:
--   Fair Selling: vbar Sum nonneg
-- statement:
--   The `v̄i`-value of a bundle is non-negative when the valuation is.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L198-L200
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L198-L200

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]

theorem FairSelling.vbarSum_nonneg {vi p : G → ℝ} (hv : ∀ g, 0 ≤ vi g) (A : Finset G) :
    0 ≤ vbarSum vi p A := by sorry
