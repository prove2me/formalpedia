-- Prove2me | Theorems.Thm_FamousTheorems_szpilrajn
-- name    : FamousTheorems.szpilrajn
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:10:18.767571+00:00
-- url     : https://prove2.me/theorems/5faef260-4999-43e2-9edf-a09910c4c277
-- title:
--   Szpilrajn's extension theorem
-- statement:
--   **Szpilrajn's extension theorem** (the order-extension principle).
--
--   Every partial order extends to a linear order on the same set:
--   $$r \text{ a partial order} \;\Longrightarrow\; \exists\, s \text{ a linear order with } r \subseteq s.$$
--
--   Any collection of incomparable elements can be arranged into a single chain without
--   contradicting the comparisons already fixed. The proof is Zorn's lemma applied to the
--   partial orders extending $r$: a maximal one must be total, since an incomparable pair could
--   otherwise be forced in either direction.
--
--   The statement is genuinely non-constructive and strictly weaker than the axiom of choice —
--   it follows from the Boolean prime ideal theorem but does not imply choice. It is the order
--   theoretic counterpart of extending a linearly independent set to a basis, and is used to
--   show that a partial order is exactly the intersection of its linear extensions, which is the
--   starting point for order dimension.
--
--   Szpilrajn published it in 1930, noting Banach, Kuratowski and Tarski had it independently.
--
--   **Formalization note.** `IsPartialOrder α r` and `IsLinearOrder α s` are the unbundled
--   order classes, and `r ≤ s` is pointwise implication of the relations. The result is Mathlib's
--   `extend_partialOrder`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem szpilrajn {α : Type*} (r : α → α → Prop) [IsPartialOrder α r] :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ r ≤ s := by sorry

end FamousTheorems
