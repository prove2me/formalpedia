-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHessR_frame
-- name    : BirkhoffGlobalSection.TangentialHessian.tHessR_frame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:43:13.274775+00:00
-- url     : https://prove2.me/theorems/08c80b4e-3f92-4e1b-9299-3770729ad46a
-- title:
--   Tangential Hessian in the quaternion frame (general mass ratio)
-- statement:
--   Let $g = \nabla K$ and $H = \operatorname{Hess} K$ be the gradient and Hessian of the Levi-Civita regularized Hamiltonian, for any $\mu$, with $r$ a free parameter. Let $F$ be the $3\times 4$ matrix whose rows are $Ig$, $Jg$, $Kg$ for the quaternion matrices of Joung–van Koert (Section 2.3). Then the symmetrized tangential Hessian satisfies
--   $$T(s) = F\,H\,F^{\mathsf T},$$
--   with $H$ written through its upper-triangular entries (it is symmetric).
--
--   This puts the tangential Hessian in the form of the quaternion-frame identity $\det(F H F^{\mathsf T}) = |g|^4\, g^{\mathsf T}\operatorname{adj}(H)\, g$. It generalizes the $\mu = 0$ statement already on the platform.
--
--   **Formalization note.** $T(s)$ is `tHessR μ c r s`; $g$, $H$ are `kGradR`, `kHessR`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4, Section 2.3.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace BirkhoffGlobalSection.TangentialHessian

/-- The tangential Hessian in the quaternion frame (any `μ`; `kHessR` is symmetric). -/
theorem tHessR_frame (μ c r : ℝ) (s : Phase) :
    tHessR μ c r s = !![kGradR μ c r s 2, kGradR μ c r s 3, -kGradR μ c r s 0, -kGradR μ c r s 1;
        kGradR μ c r s 1, -kGradR μ c r s 0, -kGradR μ c r s 3, kGradR μ c r s 2;
        -kGradR μ c r s 3, kGradR μ c r s 2, -kGradR μ c r s 1, kGradR μ c r s 0] *
      !![kHessR μ c r s 0 0, kHessR μ c r s 0 1, kHessR μ c r s 0 2, kHessR μ c r s 0 3;
        kHessR μ c r s 0 1, kHessR μ c r s 1 1, kHessR μ c r s 1 2, kHessR μ c r s 1 3;
        kHessR μ c r s 0 2, kHessR μ c r s 1 2, kHessR μ c r s 2 2, kHessR μ c r s 2 3;
        kHessR μ c r s 0 3, kHessR μ c r s 1 3, kHessR μ c r s 2 3, kHessR μ c r s 3 3] *
      (!![kGradR μ c r s 2, kGradR μ c r s 3, -kGradR μ c r s 0, -kGradR μ c r s 1;
        kGradR μ c r s 1, -kGradR μ c r s 0, -kGradR μ c r s 3, kGradR μ c r s 2;
        -kGradR μ c r s 3, kGradR μ c r s 2, -kGradR μ c r s 1, kGradR μ c r s 0] :
          Matrix (Fin 3) (Fin 4) ℝ).transpose := by sorry

end BirkhoffGlobalSection.TangentialHessian
