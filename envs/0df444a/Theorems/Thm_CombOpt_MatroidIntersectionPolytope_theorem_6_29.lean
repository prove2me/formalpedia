-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_theorem_6_29
-- name    : CombOpt.MatroidIntersectionPolytope.theorem_6_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:52.977127+00:00
-- url     : https://prove2.me/theorems/e0eb3727-6891-4304-b9dd-5098bd855cfe
-- title:
--   Theorem 6.29 — a TDI system with integral right-hand side defining a polytope gives an integral polytope
-- statement:
--   Let $Ax\le b$ be a totally dual integral rational system such that $P=\{x : Ax\le b\}$ is a polytope and $b$ is integral. Then $P$ is an integral polytope.
--
--   This is how integral min-max theorems yield integral polyhedra: total dual integrality of a system with integral right-hand side forces every vertex of its polytope to be integral. In this mission it turns Theorem 8.23 into Theorem 8.20.
--
--   **Formalization Note** $A$ and $b$ have rational entries, so $P$ is a rational polyhedron; being a polytope is stated as $l\le x\le u$ on $P$ for some $l,u$, the book's definition.
--
--   Differences from the source:
--   - encoding: A ∈ ℚ^{m×n}, b ∈ ℚ^m, rows and columns numbered 1, …, m and 1, …, n → rows and columns indexed by arbitrary finite types m, n; reason: relabelling of rows and columns; same instances
--   - encoding: P = {x : Ax ≤ b} is a rational polytope → A, b rational (so P is a rational polyhedron) and ∃ l u, l ≤ x ≤ u for all x ∈ P; reason: this is the book's definition of a polytope (p. 204); rationality is carried by the types
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.6, Theorem 6.29, p. 225 (PDF p. 233)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_polyhedron
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsTDI
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsIntegralPolyhedron

namespace CombOpt.MatroidIntersectionPolytope

/-- **Theorem 6.29** (Hoffman 1974; Edmonds–Giles 1977).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.6, Theorem 6.29, p. 225 (PDF p. 233): "Let Ax ≤ b be a totally dual integral system
such that P = {x : Ax ≤ b} is a rational polytope and b is integral. Then P is an integral
polytope."

For a rational system `Ax ≤ b` that is totally dual integral, with `b` integral and
`P = {x : Ax ≤ b}` bounded (`l ≤ x ≤ u` on `P`), `P` is an integral polyhedron.

**Formalization Note.** `A` and `b` have rational entries, so `P` is a rational polyhedron; the
remaining content of "rational polytope" is boundedness, stated as in the book's definition of a
polytope (p. 204). -/
theorem theorem_6_29 {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (b : m → ℚ)
    (hTDI : IsTDI A b) (hb : ∀ i, ∃ k : ℤ, b i = k)
    (hbdd : ∃ l u : n → ℝ, ∀ x ∈ polyhedron A b, l ≤ x ∧ x ≤ u) :
    IsIntegralPolyhedron (polyhedron A b) := by sorry

end CombOpt.MatroidIntersectionPolytope
