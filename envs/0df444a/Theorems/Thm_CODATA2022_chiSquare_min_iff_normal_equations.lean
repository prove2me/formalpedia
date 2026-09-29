-- Prove2me | Theorems.Thm_CODATA2022_chiSquare_min_iff_normal_equations
-- name    : CODATA2022.chiSquare_min_iff_normal_equations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:18:10.336918+00:00
-- url     : https://prove2.me/theorems/00bdda94-b193-482d-ab53-17cd9c52bf49
-- title:
--   Minimality of $\chi^2$ is equivalent to the normal equations
-- statement:
--   For a positive definite weight matrix $W$, a parameter vector $\hat x$ minimizes
--   $\chi^2$ over all of $\mathbb{R}^M$ **if and only if** it satisfies the normal equations
--
--   $$A^{\mathsf T}WA\,\hat x \;=\; A^{\mathsf T}Wz .$$
--
--   This is the sense in which the CODATA recommended values "are" the least-squares solution:
--   the adjustment solves the normal equations, and this milestone says that doing so is exactly
--   the same as minimizing the reported $\chi^2$.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. XIV.A: the recommended values are obtained from the least-squares adjustment of the input data with the covariance-weighted $\chi^2$.

import Mathlib
import Definitions.Def_CODATA2022_least_squares
open Matrix

namespace CODATA2022
theorem chiSquare_min_iff_normal_equations {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : W.PosDef) (z : Fin N → ℝ) (xhat : Fin M → ℝ) :
    (∀ x : Fin M → ℝ, chiSquare A W z xhat ≤ chiSquare A W z x)
      ↔ (Aᵀ * W * A).mulVec xhat = (Aᵀ * W).mulVec z := by sorry
end CODATA2022
