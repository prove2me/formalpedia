-- Prove2me | Theorems.Thm_ConeLifts_StableSet_stab_facets
-- name    : ConeLifts.StableSet.stab_facets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:19:36.282608+00:00
-- url     : https://prove2.me/theorems/bf6bcab4-8c1e-4a8f-8a8b-329651fde00b
-- title:
--   Theorem 5.2, proof — the $x_i \ge 0$ are facets of $\mathrm{STAB}(G)$, and some facet misses the origin
-- statement:
--   Let $G$ be any graph on the vertex set $\{1,\dots,n\}$ with $n \ge 1$. Then
--
--   1. for every $i$, the nonnegativity $x_i \ge 0$ defines a facet $\{x \in \mathrm{STAB}(G) : x_i = 0\}$ of $\mathrm{STAB}(G)$;
--   2. $\mathrm{STAB}(G)$ has a facet $F$ with $0 \notin F$.
--
--   These facets form the set $F'$ that indexes the columns of the submatrix $S'$ in the proof of Theorem 5.2.
--
--   **Formalization Note** Facets are `IsFacet`: nonempty, proper, exposed, of dimension one less than $\mathrm{STAB}(G)$. The hypothesis $n \ge 1$ is the paper's reading of "a graph with $n$ vertices"; for $n = 0$ the polytope is a single point and has no facets.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 19, Theorem 5.2 (proof)

import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab
import Definitions.Def_ConeLifts_StableSet_IsFacet

namespace ConeLifts.StableSet

/-- **Theorem 5.2, proof** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 19): for every graph
`G` on `{1, …, n}` with `n ≥ 1`, the `n` nonnegativities `xᵢ ≥ 0` give facets
`{x ∈ STAB(G) : xᵢ = 0}` of `STAB(G)`, and `STAB(G)` has some facet that does not touch the
origin — the two ingredients of the set of facets `F′` of the proof. The hypothesis `n ≥ 1` is
the paper's reading of "a graph with n vertices" (for `n = 0`, `STAB(G)` is a point and has no
facet). -/
theorem stab_facets {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    (∀ i : Fin n, IsFacet (stab G) {x | x ∈ stab G ∧ x i = 0}) ∧
      ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet (stab G) F ∧
        (0 : EuclideanSpace ℝ (Fin n)) ∉ F := by sorry

end ConeLifts.StableSet
