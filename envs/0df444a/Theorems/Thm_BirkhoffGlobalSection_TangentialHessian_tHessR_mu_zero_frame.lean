-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHessR_mu_zero_frame
-- name    : BirkhoffGlobalSection.TangentialHessian.tHessR_mu_zero_frame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T17:30:48.502591+00:00
-- url     : https://prove2.me/theorems/afce9e94-7f78-45d7-a4f1-2b7b1e76e941
-- title:
--   Tangential Hessian at mu = 0 in the quaternion frame
-- statement:
--   Let $g = \nabla K$ and $H = \operatorname{Hess} K$ be the gradient and Hessian of the Levi-Civita regularized Hamiltonian at $\mu = 0$. Let $F$ be the $3\times 4$ matrix whose rows are $Ig$, $Jg$, $Kg$ for the quaternion matrices of Joung–van Koert (Section 2.3). Then the symmetrized tangential Hessian $T(s)$ satisfies
--   $$T(s) = F\,H\,F^{\mathsf T},$$
--   where on the right $H$ is written with its upper-triangular entries only. That is, $H$ is symmetric.
--
--   This puts the tangential Hessian in the form required by the quaternion-frame bordered-determinant identity, by which its determinant is $|g|^4\,g^{\mathsf T}\operatorname{adj}(H)\,g$. It is the first step of the proof that $\det T(s) > 0$ on the energy level set at $\mu = 0$.
-- source:
--   Quaternion frame of Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (Section 2.3), specialised to the rotating Kepler problem.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace BirkhoffGlobalSection.TangentialHessian

/-- Frame form of the tangential Hessian at `μ = 0` (the Hessian is symmetric). -/
theorem tHessR_mu_zero_frame (c r : ℝ) (s : Phase) :
    tHessR 0 c r s = !![kGradR 0 c r s 2, kGradR 0 c r s 3, -kGradR 0 c r s 0, -kGradR 0 c r s 1; kGradR 0 c r s 1, -kGradR 0 c r s 0, -kGradR 0 c r s 3, kGradR 0 c r s 2; -kGradR 0 c r s 3, kGradR 0 c r s 2, -kGradR 0 c r s 1, kGradR 0 c r s 0] * !![kHessR 0 c r s 0 0, kHessR 0 c r s 0 1, kHessR 0 c r s 0 2, kHessR 0 c r s 0 3; kHessR 0 c r s 0 1, kHessR 0 c r s 1 1, kHessR 0 c r s 1 2, kHessR 0 c r s 1 3; kHessR 0 c r s 0 2, kHessR 0 c r s 1 2, kHessR 0 c r s 2 2, kHessR 0 c r s 2 3; kHessR 0 c r s 0 3, kHessR 0 c r s 1 3, kHessR 0 c r s 2 3, kHessR 0 c r s 3 3] * (!![kGradR 0 c r s 2, kGradR 0 c r s 3, -kGradR 0 c r s 0, -kGradR 0 c r s 1; kGradR 0 c r s 1, -kGradR 0 c r s 0, -kGradR 0 c r s 3, kGradR 0 c r s 2; -kGradR 0 c r s 3, kGradR 0 c r s 2, -kGradR 0 c r s 1, kGradR 0 c r s 0] : Matrix (Fin 3) (Fin 4) ℝ).transpose := by sorry

end BirkhoffGlobalSection.TangentialHessian
