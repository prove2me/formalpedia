-- Prove2me | Theorems.Thm_BiconvexProg_Boundary_boundary_solution
-- name    : BiconvexProg.Boundary.boundary_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:50:47.322996+00:00
-- url     : https://prove2.me/theorems/2517b999-c17a-4ab5-836f-5d663d4242ba
-- title:
--   Theorem 1 — a biconcave continuous function attains its minimum over a compact set on the boundary
-- statement:
--   Let $S \subseteq \mathbb{R}^p \times \mathbb{R}^q$ (with $p + q \ge 1$) be a nonempty compact set, and let $\varphi(x, y)$ be a real function that is continuous on $S$ and such that $\varphi(\cdot, y)$ and $\varphi(x, \cdot)$ are both concave (over $S$, in the sense of biconcavity over $S$). Then the problem
--
--   $$\min\{\varphi(x, y) : (x, y) \in S\}$$
--
--   has a solution on $\partial S$, the boundary of $S$: there is $(x^*, y^*) \in \partial S$ with $\varphi(x^*, y^*) \le \varphi(x, y)$ for all $(x, y) \in S$.
--
--   Neither $S$ nor its sections need be convex, and $\varphi$ need not be jointly concave. In particular every jointly constrained bilinear program $\min\{f(x) + x^T y + g(y)\}$ with $f, g$ concave over a compact feasible region has a boundary solution, even though it need not have an extreme-point solution.
--
--   **Formalization Note** The boundary is the topological frontier of $S$ in $\mathbb{R}^p \times \mathbb{R}^q$ (closure minus interior), not a relative boundary. The hypothesis $p + q \ge 1$ is added: for $p = q = 0$ the space is a single point, $S$ is that point, its frontier is empty and the conclusion fails; the paper works in $\mathbb{R}^p \times \mathbb{R}^q$ of positive dimension throughout. Continuity is required only on $S$. The conclusion is existence of a boundary minimizer, not that every minimizer lies on the boundary.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274, Theorem 1

import Mathlib
import Definitions.Def_BiconvexProg_Boundary_BiconcaveOn

namespace BiconvexProg.Boundary

/-- Theorem 1 (Al-Khayyal–Falk 1983, p. 274): let `φ` be continuous on a nonempty compact set
`S ⊆ ℝᵖ × ℝ^q` (with `p + q > 0`), and concave in `x` and in `y` separately over `S`. Then the
problem `min {φ(x, y) : (x, y) ∈ S}` has a solution on `∂S`. -/
theorem boundary_solution {p q : ℕ} (hpq : 0 < p + q)
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)))
    (hS : IsCompact S) (hne : S.Nonempty)
    (φ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hcont : ContinuousOn φ S) (hbi : BiconcaveOn S φ) :
    ∃ z ∈ frontier S, IsMinOn φ S z := by sorry

end BiconvexProg.Boundary
