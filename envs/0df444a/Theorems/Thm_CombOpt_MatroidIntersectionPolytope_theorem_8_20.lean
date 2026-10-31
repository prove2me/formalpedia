-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_theorem_8_20
-- name    : CombOpt.MatroidIntersectionPolytope.theorem_8_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:37.17427+00:00
-- url     : https://prove2.me/theorems/f9e91f53-c5bb-47fa-8d61-346b40b3e97e
-- title:
--   Theorem 8.20 (Matroid Intersection Polytope Theorem)
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on the same finite set $S$ with rank functions $r_1,r_2$. Then the convex hull of the characteristic vectors of the common independent sets of $M_1$ and $M_2$ is precisely the set of feasible solutions of (8.7):
--
--   $$
--   \operatorname{conv}\{\chi_J : J\in\mathcal I_1\cap\mathcal I_2\}=\big\{x\in\mathbb R^S : x(A)\le r_1(A),\ x(A)\le r_2(A)\ \text{for all } A\subseteq S,\ x\ge0\big\}.
--   $$
--
--   Equivalently, the vertices of the intersection of the two matroid polytopes are exactly their common vertices (Edmonds, 1970). Applied to the two partition matroids of a bipartite graph it gives the bipartite matching polytope.
--
--   Differences from the source:
--   - encoding: a matroid (S, I): S a finite set, I a family of subsets of S satisfying (M0)–(M2); r(A) the size of a basis of A → S a finite type, subsets Finset S, I the predicate FinMatroid.Indep with the axioms (M0)–(M2) as fields; r(A) the largest size of an independent subset of A; reason: same objects: by (M2) the largest independent subset of A has the size of every basis of A
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, Theorem 8.20, p. 298 (PDF p. 305)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_TJoin_charVec
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_intersectionLP

namespace CombOpt.MatroidIntersectionPolytope

/-- **Theorem 8.20 (Matroid Intersection Polytope Theorem)** (Edmonds 1970).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, Theorem 8.20, p. 298 (PDF p. 305): "The convex hull of the characteristic vectors
of common independent sets of M₁ and M₂ is precisely the set of feasible solutions of (8.7)."

For matroids `M₁ = (S, I₁)`, `M₂ = (S, I₂)` on a finite set `S`, the convex hull in `ℝ^S` of
`{χ_J : J ∈ I₁ ∩ I₂}` equals the set of `x` with `x(A) ≤ r₁(A)` and `x(A) ≤ r₂(A)` for all
`A ⊆ S` and `x ≥ 0`. -/
theorem theorem_8_20 {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S) :
    convexHull ℝ {x : S → ℝ | ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ x = CombOpt.TJoin.charVec J} =
      intersectionLP M₁ M₂ := by sorry

end CombOpt.MatroidIntersectionPolytope
