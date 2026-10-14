-- Prove2me | Theorems.Thm_DbarRegularity_dyadic_closedCube_subset
-- name    : DbarRegularity.dyadic_closedCube_subset
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:32:04.740166+00:00
-- url     : https://prove2.me/theorems/87bc382d-251c-409d-a09a-64459270eb63
-- title:
--   Grid cubes with intersecting interiors are nested
-- statement:
--   Let $h>0$, let $N\ge 0$ be an integer and put $H=Nh$. For $z,w\in\mathbb{Z}^d$ consider the closed cubes
--   $$Q=\prod_{i=1}^d\,[z_ih,\ z_ih+h],\qquad Q'=\prod_{i=1}^d\,[w_iH,\ w_iH+H]$$
--   of the grids of mesh $h$ and $H$ in $\mathbb{R}^d$. If the interiors of $Q$ and $Q'$ intersect, then
--   $$Q\subseteq Q'.$$
--
--   In particular, for $N=2^k$ this is the nesting property of dyadic cubes: two dyadic cubes either have disjoint interiors or one contains the other.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`, and the corner $(z_ih)_i$ is the point `WithLp.toLp 2 (fun i => (z i : ℝ) * h)`. The integer $N$ is a natural number, so $H\ge 0$; for $N=0$ the hypothesis is never satisfied.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

/-- Nesting of grid cubes: let `h > 0`, `N ∈ ℕ` and `H = N h`. If the closed cube with corner
`z h` (`z ∈ ℤ^d`) and side `h` and the closed cube with corner `w H` (`w ∈ ℤ^d`) and side `H` have
intersecting interiors, then the first cube is contained in the second. -/
theorem dyadic_closedCube_subset {d : ℕ} {h H : ℝ} (hh : 0 < h) {N : ℕ} (hH : H = N * h)
    (z w : Fin d → ℤ)
    (hne : (interior (closedCube (WithLp.toLp 2 fun i => (z i : ℝ) * h) h) ∩
      interior (closedCube (WithLp.toLp 2 fun i => (w i : ℝ) * H) H)).Nonempty) :
    closedCube (WithLp.toLp 2 fun i => (z i : ℝ) * h) h ⊆
      closedCube (WithLp.toLp 2 fun i => (w i : ℝ) * H) H := by sorry

end DbarRegularity
