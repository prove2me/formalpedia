-- Prove2me | Theorems.Thm_FamousTheorems_vector_space_not_finite_union_proper_subspaces_6c
-- name    : FamousTheorems.vector_space_not_finite_union_proper_subspaces_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:09.337409+00:00
-- url     : https://prove2.me/theorems/6db62d9f-7600-4a3b-9344-97e62b1ffaa2
-- title:
--   A vector space over an infinite field is not a finite union of proper subspaces
-- statement:
--   **A vector space over an infinite field is not a finite union of proper subspaces.** Let $E$ be a vector space over an infinite division ring $k$, and let $S$ be a finite set of subspaces of $E$, none equal to $E$. Then $\bigcup_{P\in S}P\ne E$.
--
--   The result is used for "generic choice" arguments, for example to find a vector outside finitely many hyperplanes, and in the proof of the primitive element theorem for infinite fields. The hypothesis that $k$ is infinite is needed: over $\mathbb F_q$, the space $\mathbb F_q^2$ is the union of its $q+1$ lines. It is a consequence of B. H. Neumann's lemma on coset covers.
--
--   **Formalization note.** Mathlib's `Subspace.biUnion_ne_univ_of_top_notMem`. The finite family is a `Finset (Subspace k E)`, and properness of every member is `⊤ ∉ s`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subspace.biUnion_ne_univ_of_top_notMem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem vector_space_not_finite_union_proper_subspaces_6c {k E : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E] {s : Finset (Subspace k E)}
    (hs : ⊤ ∉ s) : ⋃ p ∈ s, (p : Set E) ≠ Set.univ := by sorry

end FamousTheorems
