-- Prove2me | Theorems.Thm_AppliedComb_Flows_hall
-- name    : AppliedComb.Flows.hall
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:41:49.628259+00:00
-- url     : https://prove2.me/theorems/02e11c4d-8db2-4e5a-ae9b-6d93fc2ca73f
-- title:
--   Theorem 14.7 — Hall's Theorem (bipartite graph form)
-- statement:
--   Let $G = (V, E)$ be a finite bipartite graph with bipartition $V = V_1 \cup V_2$. There is a matching which saturates all vertices of $V_1$ if and only if for every subset $A \subseteq V_1$ the set $N(A) \subseteq V$ of neighbors of the vertices in $A$ satisfies
--   $$|N(A)| \ge |A|.$$
--
--   The book states the theorem without proof, as the combinatorial content of the maximum-flow computation for the network built from a bipartite graph. It is equivalent to the existence of a system of distinct representatives (Hall, 1935).
--
--   **Formalization Note.** Bipartitions, matchings, saturation and neighbor sets are those of `AppliedComb.Flows.Matching`. The same result in its indexed-family form (a family of finite sets has an injective choice function iff every subfamily's union is at least as large as the subfamily) is Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`; this statement is the book's graph form.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 283, Theorem 14.7 (Hall's Theorem)

import Mathlib
import Definitions.Def_AppliedComb_Flows_Matching

namespace AppliedComb.Flows

/-- **Theorem 14.7 (Hall's Theorem)** (Keller & Trotter, *Applied Combinatorics*, 2017 Edition,
p. 283). Let `G = (V, E)` be a (finite) bipartite graph with `V = V₁ ∪ V₂`. There is a matching
which saturates all vertices of `V₁` if and only if for every subset `A ⊆ V₁`, the set `N ⊆ V` of
neighbors of the vertices in `A` satisfies `|N| ≥ |A|`. -/
theorem hall {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V₁ V₂ : Finset V)
    (hbip : IsBipartition G V₁ V₂) :
    (∃ M : Set (Sym2 V), IsMatching G M ∧ ∀ v ∈ V₁, Saturates M v) ↔
      ∀ A : Finset V, A ⊆ V₁ → A.card ≤ (neighborsOf G A).card := by sorry

end AppliedComb.Flows
