-- Prove2me | Theorems.Thm_FairSelling_vbarSum_eq_sum_of_price_zero
-- name    : FairSelling.vbarSum_eq_sum_of_price_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:26.031825+00:00
-- url     : https://prove2.me/theorems/75e90dc1-3814-4729-a088-239ea183d5dc
-- title:
--   Fair Selling: vbar Sum eq sum of price zero
-- statement:
--   On goods with zero price, `v̄ᵢ` agrees with `vᵢ` (for non-negative valuations).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L77-L81
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L77-L81

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.vbarSum_eq_sum_of_price_zero {vi p : G → ℝ} {A : Finset G} (hv : ∀ g, 0 ≤ vi g)
    (hp : ∀ g ∈ A, p g = 0) : vbarSum vi p A = ∑ g ∈ A, vi g := by sorry
