-- Prove2me | Theorems.Thm_FairChores_exists_outcome_of_preAlloc
-- name    : FairChores.exists_outcome_of_preAlloc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:59.319298+00:00
-- url     : https://prove2.me/theorems/d44ac715-1fd2-4936-9f5f-3c72810623b3
-- title:
--   Fair Chores: exists outcome of pre Alloc
-- statement:
--   A self-service allocation of *all* the chores induces a feasible outcome, in which agent
--   `i` pays for the chores of its own bundle that it prefers to outsource; its cost is then
--   `c̄ᵢ(bundle i) + share i`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean#L58-L138
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean#L58-L138

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.exists_outcome_of_preAlloc (P : PreAlloc T n) (p : T → ℝ) (c : Fin n → T → ℝ)
    (hp : ∀ t, 0 ≤ p t)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P.bundle i) (P.bundle j))
    (houts : ∀ i, Disjoint P.outs (P.bundle i))
    (hcover : P.outs ∪ Finset.univ.biUnion P.bundle = Finset.univ)
    (hshare : ∀ i, 0 ≤ P.share i)
    (hsum : ∑ i, P.share i = ∑ t ∈ P.outs, p t) :
    ∃ o : Outcome T n, o.Valid p ∧
      ∀ i, cost (c i) o i = cbarSum (c i) p (P.bundle i) + P.share i := by sorry
