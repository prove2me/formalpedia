-- Prove2me | Theorems.Thm_FamousTheorems_vector_space_has_basis_7b
-- name    : FamousTheorems.vector_space_has_basis_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:40.163369+00:00
-- url     : https://prove2.me/theorems/e9c25d23-15ef-4d09-98a2-6c1fe68893b5
-- title:
--   Every vector space has a basis
-- statement:
--   **Every vector space has a basis.** Let $V$ be a vector space over a division ring $K$. Then there is a subset $s\subseteq V$ that is a basis of $V$: $s$ is linearly independent and spans $V$.
--
--   For infinite-dimensional spaces the proof uses Zorn's lemma to obtain a maximal linearly independent set, which then spans. The statement is in fact equivalent to the axiom of choice (Blass, 1984). It shows that every vector space is free, that every subspace has a complement, and, for example, that $\mathbb R$ has a Hamel basis over $\mathbb Q$.
--
--   **Formalization note.** Mathlib's `Module.Basis.ofVectorSpace`, which also underlies the instance `Module.Free.of_divisionRing`. `Module.Basis s K V` is the type of bases of $V$ indexed by the elements of $s$, and the statement asserts that it is nonempty for some $s$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.Free.of_divisionRing`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem vector_space_has_basis_7b (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] : ∃ s : Set V, Nonempty (Module.Basis s K V) := by sorry

end FamousTheorems
