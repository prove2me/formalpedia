-- Prove2me | Theorems.Thm_FairChores_PreAlloc_bundle_subset
-- name    : FairChores.PreAlloc.bundle_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:54.495063+00:00
-- url     : https://prove2.me/theorems/5b5eae97-44db-4f97-94fb-19b3d5773eaa
-- title:
--   Pre Alloc: bundle subset
-- statement:
--   The Pre Alloc construction uses the bundle subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean#L42-L46
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean#L42-L46

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T]

theorem FairChores.PreAlloc.bundle_subset {P : PreAlloc T n} {p : T → ℝ} {A : Finset (Fin n)} {R : Finset T}
    (h : P.Splits p A R) (i : Fin n) : P.bundle i ⊆ R := by sorry
