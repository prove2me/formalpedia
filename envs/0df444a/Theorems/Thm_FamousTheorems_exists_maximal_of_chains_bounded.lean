-- Prove2me | Theorems.Thm_FamousTheorems_exists_maximal_of_chains_bounded
-- name    : FamousTheorems.exists_maximal_of_chains_bounded
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:35.126309+00:00
-- url     : https://prove2.me/theorems/71b96784-f230-4d79-b661-3b19ccefda3c
-- title:
--   Zorn's lemma
-- statement:
--   **Zorn's lemma.** If every chain in a partially ordered set has an upper bound, the set has a maximal element. The hypothesis quantifies over all totally ordered subsets, including the empty chain, whose upper bound is what supplies nonemptiness. Zorn's lemma is equivalent to the axiom of choice and to the well-ordering theorem, and it is the form of choice most used in algebra because it applies directly: maximal ideals, bases of arbitrary vector spaces, algebraic closures, ultrafilters and the Hahn-Banach extension all come from a single application. It is non-constructive in an essential way, producing an element no procedure can exhibit. **Formalization note.** Chains are expressed with `IsChain` and boundedness as an upper bound in the ambient order. The result is Mathlib's `exists_maximal_of_chains_bounded`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_maximal_of_chains_bounded :
    ∀ {α : Type u_1} {r : α → α → Prop}, 
    (∀ (c : Set α), IsChain r c → ∃ ub, ∀ a ∈ c, r a ub) → 
    (∀ {a b c : α}, r a b → r b c → r a c) → ∃ m, ∀ (a : α), r m a → r a m := by sorry

end FamousTheorems
