-- Prove2me | Theorems.Thm_DbarRegularity_dist_le_of_mem_closedCube
-- name    : DbarRegularity.dist_le_of_mem_closedCube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:46:00.622144+00:00
-- url     : https://prove2.me/theorems/a2cda7a3-8cb9-444c-8714-073bcd224d88
-- title:
--   Diameter bound for a closed cube in ℝ^d
-- statement:
--   Let $Q(a,s)=\{x\in\mathbb{R}^d:\ a_i\le x_i\le a_i+s\ \forall i\}$ be a closed cube in $\mathbb{R}^d$. If $x,y\in Q(a,s)$, then
--   $$|y-x|\le\sqrt d\; s,$$
--   where $|\cdot|$ is the Euclidean norm. That is, the diameter of a cube of side $s$ is at most $\sqrt d\,s$.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` and the distance is the Euclidean `dist`. No sign condition on $s$ is assumed: if the cube is nonempty and $d\ge1$ then $s\ge0$ automatically, and for $d=0$ both sides vanish.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

/-- Two points of a closed cube of side `s` in `ℝ^d` are at Euclidean distance at most `√d · s`. -/
theorem dist_le_of_mem_closedCube {d : ℕ} {a x y : EuclideanSpace ℝ (Fin d)} {s : ℝ}
    (hx : x ∈ closedCube a s) (hy : y ∈ closedCube a s) : dist y x ≤ Real.sqrt d * s := by sorry

end DbarRegularity
