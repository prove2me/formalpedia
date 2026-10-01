-- Prove2me | Theorems.Thm_ConeLifts_StableSet_stab_extremePoints
-- name    : ConeLifts.StableSet.stab_extremePoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:18:58.67922+00:00
-- url     : https://prove2.me/theorems/c57c32d3-8050-45e0-bfc0-7bfe1a5ac1c8
-- title:
--   Theorem 5.2, proof — the origin and $e_1, \dots, e_n$ are vertices of every $\mathrm{STAB}(G)$
-- statement:
--   Let $G$ be any graph on the vertex set $\{1,\dots,n\}$. Then the origin and all standard basis vectors $e_1, \dots, e_n$ of $\mathbb R^n$ are vertices (extreme points) of the stable set polytope:
--
--   $$
--   0 \in \mathrm{ext}\,\mathrm{STAB}(G), \qquad e_i \in \mathrm{ext}\,\mathrm{STAB}(G) \quad (i = 1,\dots,n).
--   $$
--
--   They are the incidence vectors of the empty set and of the singletons, which are stable in every graph. These $n+1$ vertices index the rows of the submatrix $S'$ of the slack matrix used in the proof of Theorem 5.2.
--
--   **Formalization Note** A vertex is an element of `Set.extremePoints ℝ (stab G)`, and $e_i$ is `EuclideanSpace.single i 1`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 19, Theorem 5.2 (proof)

import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab

namespace ConeLifts.StableSet

/-- **Theorem 5.2, proof** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 19): the origin and
all standard basis vectors `e₁, …, eₙ` are vertices of `STAB(G)`, for every graph `G` on
`{1, …, n}` — "the empty set and all singleton vertices are stable in any graph". A vertex of the
polytope is an extreme point (`Set.extremePoints ℝ`); `eᵢ` is `EuclideanSpace.single i 1`. -/
theorem stab_extremePoints {n : ℕ} (G : SimpleGraph (Fin n)) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ Set.extremePoints ℝ (stab G) ∧
      ∀ i : Fin n, EuclideanSpace.single i (1 : ℝ) ∈ Set.extremePoints ℝ (stab G) := by sorry

end ConeLifts.StableSet
