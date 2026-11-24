-- Prove2me | Theorems.Thm_FairChores_bagfill_exists
-- name    : FairChores.bagfill_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:06.522629+00:00
-- url     : https://prove2.me/theorems/6d25e354-3c18-4e85-ae86-e08f7f5cd23b
-- title:
--   Fair Chores: bagfill exists
-- statement:
--   **Bag-filling for chores with outsourcing.**  If every active agent satisfies the
--   invariant, the remaining chores can be allocated among the active agents so that every one of
--   them has cost at most twice its threshold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L72-L290
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L72-L290

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
import Definitions.Def_RequestProject_ChoresBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}
omit [Fintype T]

theorem FairChores.bagfill_exists (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i) :
    ∀ (k : ℕ) (A : Finset (Fin n)) (R : Finset T), A.card = k → A.Nonempty →
      (∀ i ∈ A, Inv c p mu i A.card R) →
      ∃ P : PreAlloc T n, P.Splits p A R ∧
        ∀ i ∈ A, cbarSum (c i) p (P.bundle i) + P.share i ≤ 2 * mu i := by sorry
