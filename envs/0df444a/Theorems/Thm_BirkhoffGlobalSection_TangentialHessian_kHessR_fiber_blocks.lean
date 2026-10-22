-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_kHessR_fiber_blocks
-- name    : BirkhoffGlobalSection.TangentialHessian.kHessR_fiber_blocks
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:43:08.215922+00:00
-- url     : https://prove2.me/theorems/a50ed6c9-f1eb-47ca-8cc5-a9284730e174
-- title:
--   Block-diagonal Hessian of the Levi-Civita Hamiltonian in the shifted momentum
-- statement:
--   Let $g = \nabla K$ and $H = \operatorname{Hess} K$ for the Levi-Civita regularized Hamiltonian, with $u = (g_2, g_3)$, $P = (H_{i,j+2})_{i,j}$, $L = H_{zz} - PP^{\mathsf T}$ and $v = (g_0, g_1) - Pu$ as in the block formula for the bordered form. Then, for all $\mu, c, r, s$,
--   $$L = L_0(z) + u_1 M_1 + u_2 M_2, \qquad v = v(z),$$
--   where $M_1 = \operatorname{Hess} b_1$ and $M_2 = \operatorname{Hess} b_2$ for $b(z) = (-(2Z+\mu)z_2,\, (2Z-\mu)z_1)$, and $L_0 = -\tfrac12\operatorname{Hess} F$, $v = -\tfrac12 \nabla F$ depend on $z$ (and $\mu, c, r$) only.
--
--   This makes the Hessian block-diagonal in the shifted momentum $u = w + b(z)$: $\operatorname{Hess}K = J^{\mathsf T}\operatorname{diag}(L, I) J$ with $L = \sum_i u_i \operatorname{Hess} b_i - \tfrac12 \operatorname{Hess} F$. See Grisa's companion paper, Zenodo 21376299, §5.
--
--   **Formalization note.** The five entry identities are stated separately; $L_0$ and $v$ are `fibL00`, `fibL01`, `fibL11`, `fibV0`, `fibV1`.
-- source:
--   Grisa, companion paper, Zenodo 21376299 (2026), §5 (block-diagonal Hessian).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace BirkhoffGlobalSection.TangentialHessian

/-- `L = L₀ + u₁ M₁ + u₂ M₂` and `v = g_z - P u`, entrywise, for every `r`. -/
theorem kHessR_fiber_blocks (μ c r : ℝ) (s : Phase) :
    kHessR μ c r s 0 0 - kHessR μ c r s 0 2 ^ 2 - kHessR μ c r s 0 3 ^ 2
        = fibL00 μ c r s + kGradR μ c r s 2 * (-4 * s 1) + kGradR μ c r s 3 * (12 * s 0) ∧
    kHessR μ c r s 1 1 - kHessR μ c r s 1 2 ^ 2 - kHessR μ c r s 1 3 ^ 2
        = fibL11 μ c r s + kGradR μ c r s 2 * (-12 * s 1) + kGradR μ c r s 3 * (4 * s 0) ∧
    kHessR μ c r s 0 1 - kHessR μ c r s 0 2 * kHessR μ c r s 1 2 - kHessR μ c r s 0 3 * kHessR μ c r s 1 3
        = fibL01 μ r s + kGradR μ c r s 2 * (-4 * s 0) + kGradR μ c r s 3 * (4 * s 1) ∧
    kGradR μ c r s 0 - kHessR μ c r s 0 2 * kGradR μ c r s 2 - kHessR μ c r s 0 3 * kGradR μ c r s 3
        = fibV0 μ c r s ∧
    kGradR μ c r s 1 - kHessR μ c r s 1 2 * kGradR μ c r s 2 - kHessR μ c r s 1 3 * kGradR μ c r s 3
        = fibV1 μ c r s := by sorry

end BirkhoffGlobalSection.TangentialHessian
