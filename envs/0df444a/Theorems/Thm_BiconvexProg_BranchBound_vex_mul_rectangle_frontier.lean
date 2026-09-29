-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_vex_mul_rectangle_frontier
-- name    : BiconvexProg.BranchBound.vex_mul_rectangle_frontier
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:54:25.128001+00:00
-- url     : https://prove2.me/theorems/7c3d8466-d9af-44d6-b80f-c92ae8439d99
-- title:
--   Theorem 3 — $\mathrm{Vex}_\Omega\, xy = xy$ on the boundary of a rectangle
-- statement:
--   Let $\Omega = \{(x,y) : l \le x \le L,\ m \le y \le M\} \subseteq \mathbb{R}^2$ be a rectangle. Then
--
--   $$\mathrm{Vex}_\Omega\, xy = xy \qquad \text{for all } (x, y) \in \partial\Omega,$$
--
--   where $\partial\Omega$ is the topological boundary of $\Omega$ in $\mathbb{R}^2$.
--
--   The convex envelope of the bilinear term is therefore exact on the edges of the rectangle. This is why splitting a rectangle at a point makes the new subproblems exact at that point in the split coordinate.
--
--   **Formalization Note** $\partial\Omega$ is Mathlib's `frontier` in $\mathbb{R} \times \mathbb{R}$, whose product topology is the Euclidean one. For a degenerate rectangle ($l = L$ or $m = M$) the boundary is the whole rectangle, and the statement still holds.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 276, Theorem 3

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace BiconvexProg.BranchBound

/-- Theorem 3 (p. 276): on a rectangle `Ω = [l, L] × [m, M] ⊂ ℝ²`, the convex envelope of `xy`
equals `xy` at every point of the boundary `∂Ω`. -/
theorem vex_mul_rectangle_frontier (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ frontier (Set.Icc l L ×ˢ Set.Icc m M)) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => q.1 * q.2) p = p.1 * p.2 := by sorry

end BiconvexProg.BranchBound
