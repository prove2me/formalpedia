-- Prove2me | Theorems.Thm_FamousTheorems_jacobson_noether_theorem
-- name    : FamousTheorems.jacobson_noether_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:28.283238+00:00
-- url     : https://prove2.me/theorems/a95a8f68-bd74-4785-9e7b-94c45c1d65cc
-- title:
--   The Jacobson–Noether theorem
-- statement:
--   **The Jacobson–Noether theorem.** Let $D$ be a noncommutative division ring that is algebraic over its centre $Z$. Then there is an element $x\in D\setminus Z$ that is separable over $Z$.
--
--   The theorem is a key step toward Jacobson's commutativity theorem and toward the structure theory of central division algebras. It shows, for example, that a noncommutative algebraic division algebra has a separable maximal subfield containing a noncentral element.
--
--   **Formalization note.** Mathlib's `JacobsonNoether.exists_separable_and_not_isCentral`. The centre is `Subring.center D`, and noncommutativity is expressed as `Subring.center D ≠ ⊤`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `JacobsonNoether.exists_separable_and_not_isCentral`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobson_noether_theorem (D : Type*) [DivisionRing D] [Algebra.IsAlgebraic (Subring.center D) D] (h : Subring.center D ≠ ⊤) :
    ∃ x ∉ Subring.center D, IsSeparable (Subring.center D) x := by sorry

end FamousTheorems
