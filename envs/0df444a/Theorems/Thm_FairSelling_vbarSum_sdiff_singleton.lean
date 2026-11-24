-- Prove2me | Theorems.Thm_FairSelling_vbarSum_sdiff_singleton
-- name    : FairSelling.vbarSum_sdiff_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:29:53.114799+00:00
-- url     : https://prove2.me/theorems/e52ef651-ddbc-42a1-8f3d-5817054ef9b9
-- title:
--   Fair Selling: vbar Sum sdiff singleton
-- statement:
--   Removing one good from a bundle, measured with `v̄i`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L179-L186
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L179-L186

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]

theorem FairSelling.vbarSum_sdiff_singleton {vi p : G → ℝ} {A : Finset G} {g : G} (hg : g ∈ A) :
    vbarSum vi p A = vbarSum vi p (A \ {g}) + vbar vi p g := by sorry
