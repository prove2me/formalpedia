-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_vex_mul_rectangle
-- name    : BiconvexProg.BranchBound.vex_mul_rectangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T17:53:59.038864+00:00
-- url     : https://prove2.me/theorems/bb316769-5081-423b-85ae-8817fc3c71e6
-- title:
--   Theorem 2 — $\mathrm{Vex}_\Omega\, xy = \max\{mx + ly - lm,\ Mx + Ly - LM\}$ on a rectangle
-- statement:
--   Let $\Omega = \{(x,y) : l \le x \le L,\ m \le y \le M\} \subseteq \mathbb{R}^2$ be a rectangle. Then for every $(x, y) \in \Omega$,
--
--   $$\mathrm{Vex}_\Omega\, xy = \max\{\, mx + ly - lm,\ Mx + Ly - LM \,\},$$
--
--   where $\mathrm{Vex}_\Omega$ is the convex envelope over $\Omega$ (the pointwise supremum of all convex functions underestimating $xy$ on $\Omega$).
--
--   This closed form, now known as the McCormick envelope, gives the lower-bounding functions of the branch-and-bound algorithm: the node function of every subproblem is a sum of such maxima of two affine functions.
--
--   **Formalization Note** The identity is stated at the points of $\Omega$, where the envelope is meaningful. Degenerate rectangles ($l = L$ or $m = M$) are included, and the identity holds for them too. No hypothesis $l \le L$, $m \le M$ is needed, since the statement is empty otherwise.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 275, Theorem 2

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace BiconvexProg.BranchBound

/-- Theorem 2 (p. 275): on a rectangle `Ω = [l, L] × [m, M] ⊂ ℝ²`, the convex envelope of `xy` is
`max {mx + ly − lm, Mx + Ly − LM}`, at every point of `Ω`. -/
theorem vex_mul_rectangle (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc l L ×ˢ Set.Icc m M) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => q.1 * q.2) p =
      max (m * p.1 + l * p.2 - l * m) (M * p.1 + L * p.2 - L * M) := by sorry

end BiconvexProg.BranchBound
