-- Prove2me | Theorems.Thm_FairChores_PreAlloc_outs_subset
-- name    : FairChores.PreAlloc.outs_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:17:56.125462+00:00
-- url     : https://prove2.me/theorems/998f5a47-ad5c-4aff-815b-ad1ebbe6b28d
-- title:
--   Pre Alloc: outs subset
-- statement:
--   The Pre Alloc construction uses the outs subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean#L49-L53
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean#L49-L53

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T]

theorem FairChores.PreAlloc.outs_subset {P : PreAlloc T n} {p : T → ℝ} {A : Finset (Fin n)} {R : Finset T}
    (h : P.Splits p A R) : P.outs ⊆ R := by sorry
