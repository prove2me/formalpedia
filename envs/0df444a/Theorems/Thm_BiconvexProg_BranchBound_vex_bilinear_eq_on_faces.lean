-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_vex_bilinear_eq_on_faces
-- name    : BiconvexProg.BranchBound.vex_bilinear_eq_on_faces
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:55:48.187975+00:00
-- url     : https://prove2.me/theorems/2cc0cd36-aee1-4c49-816b-abdea673fecd
-- title:
--   Corollary (second clause, corrected) — $x^\top y = \mathrm{Vex}_\Omega\, x^\top y$ where every $(x_i,y_i)$ lies on $\partial\Omega_i$
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n \times \mathbb{R}^n$ be a box with coordinate rectangles $\Omega_i \subseteq \mathbb{R}^2$. If $(x, y)$ is a point whose coordinate pairs all lie on the boundaries of their rectangles, $(x_i, y_i) \in \partial\Omega_i$ for **every** $i = 1, \dots, n$, then
--
--   $$x^\top y = \mathrm{Vex}_\Omega\, x^\top y .$$
--
--   Along the algorithm, the split point is a corner of the split coordinate's new rectangles in all four children. The children's underestimates are therefore exact there in that coordinate.
--
--   **Formalization Note** This corrects a printed slip. The paper states the clause "for all $(x, y) \in \partial\Omega$", which is false for $n \ge 2$. Take $n = 2$, $\Omega_1 = \Omega_2 = [0,2]^2$, $x = (0,1)$, $y = (0,1)$. The point lies on $\partial\Omega$ because $x_1 = l_1$, but $\mathrm{Vex}_\Omega\, x^\top y = \mathrm{Vex}_{\Omega_1}(0 \cdot 0) + \mathrm{Vex}_{\Omega_2}(1\cdot 1) = 0 + \max\{0, 0\} = 0 \ne 1 = x^\top y$. The corrected clause requires the boundary condition in every coordinate. That condition implies $(x,y) \in \Omega$.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 276, Corollary (second clause, corrected)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

/-- Corollary, second clause, corrected (p. 276): `xᵀy = Vex_Ω xᵀy` at every point `(x, y)` of the
box `Ω` whose coordinate pair `(x_i, y_i)` lies on the boundary `∂Ω_i` of its rectangle for
**every** `i`. (As printed, "for all `(x, y) ∈ ∂Ω`", the clause is false for `n ≥ 2`.) -/
theorem vex_bilinear_eq_on_faces {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hface : ∀ i, (z.1 i, z.2 i) ∈ frontier (Ω.rect i)) :
    convexEnvelope Ω.toSet bilin z = bilin z := by sorry

end BiconvexProg.BranchBound
