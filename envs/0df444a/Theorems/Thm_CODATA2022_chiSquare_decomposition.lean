-- Prove2me | Theorems.Thm_CODATA2022_chiSquare_decomposition
-- name    : CODATA2022.chiSquare_decomposition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:17:46.626397+00:00
-- url     : https://prove2.me/theorems/ec2b5bf8-d695-4dae-9d77-a97cfbff99bf
-- title:
--   $\chi^2(x) = \chi^2(\hat x) + (x-\hat x)^{\mathsf T}A^{\mathsf T}WA(x-\hat x)$
-- statement:
--   The algebraic identity underlying the whole adjustment. If $\hat x$ solves the
--   normal equations $A^{\mathsf T}WA\hat x = A^{\mathsf T}Wz$ and the weight matrix $W$ is
--   symmetric, then for every parameter vector $x$
--
--   $$\chi^2(x) \;=\; \chi^2(\hat x) \;+\; (x-\hat x)^{\mathsf T}A^{\mathsf T}WA\,(x-\hat x).$$
--
--   The cross terms cancel precisely because of the normal equations, which is why $\chi^2$ at
--   the fitted values is the residual chi-square reported by the adjustment and why any
--   departure from $\hat x$ can only increase it when $A^{\mathsf T}WA$ is positive
--   semidefinite.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. XIV.A (least-squares adjustment; $\chi^2$ of the 2022 adjustment) and Nomenclature entry for $\chi^2$.

import Mathlib
import Definitions.Def_CODATA2022_least_squares
open Matrix

namespace CODATA2022
theorem chiSquare_decomposition {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : W.IsHermitian) (z : Fin N → ℝ) (xhat x : Fin M → ℝ)
    (hnormal : (Aᵀ * W * A).mulVec xhat = (Aᵀ * W).mulVec z) :
    chiSquare A W z x
      = chiSquare A W z xhat + (x - xhat) ⬝ᵥ (Aᵀ * W * A).mulVec (x - xhat) := by sorry
end CODATA2022
