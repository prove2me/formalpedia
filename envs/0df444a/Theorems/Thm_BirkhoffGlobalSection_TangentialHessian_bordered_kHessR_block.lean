-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_bordered_kHessR_block
-- name    : BirkhoffGlobalSection.TangentialHessian.bordered_kHessR_block
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:42:45.805849+00:00
-- url     : https://prove2.me/theorems/487decf2-bc40-40ec-9a4c-728b6fbeaef3
-- title:
--   Block form of the bordered Hessian of the Levi-Civita Hamiltonian
-- statement:
--   Let $g = \nabla K$ and $H = \operatorname{Hess} K$ be the gradient and Hessian of the Levi-Civita regularized Hamiltonian $K_{\mu,c} = P_{\mu,c} - \mu Z/r$, in the coordinates $s = (z_1, z_2, w_1, w_2)$ with $r$ a free parameter. Then, for all $\mu, c, r, s$,
--   $$g^{\mathsf T} \operatorname{adj}(H)\, g = |u|^2 \det L + v^{\mathsf T} \operatorname{adj}(L)\, v ,$$
--   where $u = (g_2, g_3)$, $P = (H_{i,j+2})_{i,j}$, $L = H_{zz} - P P^{\mathsf T}$ and $v = (g_0, g_1) - P u$.
--
--   The $w$-block of $\operatorname{Hess} K$ is the identity: $K$ is $\tfrac12|w|^2$ plus terms at most linear in $w$. So the general block formula for bordered forms applies. The left side is the bordered form whose positivity, times $|g|^4$, is the tangential-Hessian determinant of Joung–van Koert, Proposition 4.4. The formula holds for every $r$, with no constraint linking $r$ to $z$.
--
--   **Formalization note.** $g$ and $H$ are `kGradR μ c r s` and `kHessR μ c r s`; the right side is written out in their entries.
-- source:
--   Grisa, companion paper, Zenodo 21376299 (2026), §5 (block-diagonal Hessian); Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.LinearAlgebra.Matrix.Adjugate
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace BirkhoffGlobalSection.TangentialHessian

/-- (a) + (b): the bordered form of the Levi-Civita Hamiltonian, for every `μ, c, r`. -/
theorem bordered_kHessR_block (μ c r : ℝ) (s : Phase) :
    kGradR μ c r s ⬝ᵥ (kHessR μ c r s).adjugate.mulVec (kGradR μ c r s) =
      (kGradR μ c r s 2 ^ 2 + kGradR μ c r s 3 ^ 2) *
          ((kHessR μ c r s 0 0 - kHessR μ c r s 0 2 ^ 2 - kHessR μ c r s 0 3 ^ 2) *
              (kHessR μ c r s 1 1 - kHessR μ c r s 1 2 ^ 2 - kHessR μ c r s 1 3 ^ 2)
            - (kHessR μ c r s 0 1 - kHessR μ c r s 0 2 * kHessR μ c r s 1 2
                - kHessR μ c r s 0 3 * kHessR μ c r s 1 3) ^ 2) +
        ((kHessR μ c r s 1 1 - kHessR μ c r s 1 2 ^ 2 - kHessR μ c r s 1 3 ^ 2) *
            (kGradR μ c r s 0 - kHessR μ c r s 0 2 * kGradR μ c r s 2
              - kHessR μ c r s 0 3 * kGradR μ c r s 3) ^ 2
          - 2 * (kHessR μ c r s 0 1 - kHessR μ c r s 0 2 * kHessR μ c r s 1 2
                - kHessR μ c r s 0 3 * kHessR μ c r s 1 3) *
              (kGradR μ c r s 0 - kHessR μ c r s 0 2 * kGradR μ c r s 2
                - kHessR μ c r s 0 3 * kGradR μ c r s 3) *
              (kGradR μ c r s 1 - kHessR μ c r s 1 2 * kGradR μ c r s 2
                - kHessR μ c r s 1 3 * kGradR μ c r s 3)
          + (kHessR μ c r s 0 0 - kHessR μ c r s 0 2 ^ 2 - kHessR μ c r s 0 3 ^ 2) *
            (kGradR μ c r s 1 - kHessR μ c r s 1 2 * kGradR μ c r s 2
              - kHessR μ c r s 1 3 * kGradR μ c r s 3) ^ 2) := by sorry

end BirkhoffGlobalSection.TangentialHessian
