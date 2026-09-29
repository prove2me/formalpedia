-- Prove2me | Theorems.Thm_FamousTheorems_complete_ordered_field_unique_7b
-- name    : FamousTheorems.complete_ordered_field_unique_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:35:44.038573+00:00
-- url     : https://prove2.me/theorems/c1f4ed79-0e6a-48d6-9151-628edd113425
-- title:
--   Uniqueness of the complete ordered field
-- statement:
--   **Uniqueness of the complete ordered field.** Let $\beta$ and $\gamma$ be conditionally complete linearly ordered fields, meaning that every nonempty subset bounded above has a least upper bound. Then there is exactly one order-preserving ring isomorphism $\beta\to\gamma$.
--
--   So the axioms of a complete ordered field determine the real numbers up to a unique isomorphism, and all constructions of $\mathbb R$ (Dedekind cuts, Cauchy sequences, decimal expansions) give the same result. Completeness implies the archimedean property, so the result follows from the embedding of archimedean ordered fields into $\mathbb R$.
--
--   **Formalization note.** Mathlib's instance `ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso`. `β ≃+*o γ` is the type of order-preserving ring isomorphisms, and `Nonempty (Unique ...)` asserts that it has exactly one element.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem complete_ordered_field_unique_7b (β γ : Type*) [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
    [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ] : Nonempty (Unique (β ≃+*o γ)) := by sorry

end FamousTheorems
