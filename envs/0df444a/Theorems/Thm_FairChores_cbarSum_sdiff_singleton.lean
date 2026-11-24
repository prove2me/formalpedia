-- Prove2me | Theorems.Thm_FairChores_cbarSum_sdiff_singleton
-- name    : FairChores.cbarSum_sdiff_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:13.405796+00:00
-- url     : https://prove2.me/theorems/bd5f09df-adb8-4089-b34e-d5dab66605a5
-- title:
--   Fair Chores: cbar Sum sdiff singleton
-- statement:
--   Removing one chore from a bundle, measured with `c̄ᵢ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L159-L166
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L159-L166

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T]

theorem FairChores.cbarSum_sdiff_singleton {A : Finset T} {t : T} (ht : t ∈ A) :
    cbarSum ci p A = cbarSum ci p (A \ {t}) + cbar ci p t := by sorry
