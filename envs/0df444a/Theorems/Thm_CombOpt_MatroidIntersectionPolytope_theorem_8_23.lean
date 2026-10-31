-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_theorem_8_23
-- name    : CombOpt.MatroidIntersectionPolytope.theorem_8_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:50.997214+00:00
-- url     : https://prove2.me/theorems/49832320-f5dd-400a-9c17-87bb816b0764
-- title:
--   Theorem 8.23 — the matroid intersection system (8.7) is totally dual integral
-- statement:
--   Let $M_1,M_2$ be matroids on $S$ with rank functions $r_1,r_2$. The rational system (8.7),
--
--   $$
--   x(A)\le r_1(A),\quad x(A)\le r_2(A)\quad\text{for all } A\subseteq S,\qquad -x_e\le0\quad\text{for all } e\in S,
--   $$
--
--   is **totally dual integral**: for every integral $w\in\mathbb Z^S$ for which the optima in $\max\{w^Tx : Ax\le b\}=\min\{y^Tb : y^TA=w^T,\ y\ge0\}$ exist, the minimum is achieved by an integral $y$.
--
--   With Theorem 6.29 and the integrality of the ranks this gives that (8.7) defines an integral polytope, which is Theorem 8.20.
--
--   Differences from the source:
--   - encoding: a matroid (S, I): S a finite set, I a family of subsets of S satisfying (M0)–(M2); r(A) the size of a basis of A → S a finite type, subsets Finset S, I the predicate FinMatroid.Indep with the axioms (M0)–(M2) as fields; r(A) the largest size of an independent subset of A; reason: same objects: by (M2) the largest independent subset of A has the size of every basis of A
--   - encoding: the system (8.7) with constraints x_e ≥ 0 → the system Ax ≤ b with rows (1, A), (2, A) for each A ⊆ S and a row −x_e ≤ 0 for each e ∈ S (system87Matrix, system87Rhs); reason: the book's TDI definition is for systems Ax ≤ b; this lists the rows of (8.7) as written, and the sanity file proves its solution set is the set (8.7)
--   - reading: for each integral w for which the optima exist → for each integral w such that both the maximum and the minimum of (6.13) are attained; reason: by LP duality either optimum existing implies the other, so this is no stronger
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, Theorem 8.23, p. 299 (PDF p. 306)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_polyhedron
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsTDI
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_system87Matrix
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_system87Rhs

namespace CombOpt.MatroidIntersectionPolytope

/-- **Theorem 8.23** (total dual integrality of (8.7)).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, Theorem 8.23, p. 299 (PDF p. 306): "The system (8.7) is totally dual integral."

The rational system `Ax ≤ b` of (8.7), with one row `x(A) ≤ rᵢ(A)` for each `i ∈ {1, 2}` and each
`A ⊆ S` and one row `−x_e ≤ 0` for each `e ∈ S`, is totally dual integral in the sense of
p. 225. -/
theorem theorem_8_23 {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S) :
    IsTDI (system87Matrix (S := S)) (system87Rhs M₁ M₂) := by sorry

end CombOpt.MatroidIntersectionPolytope
