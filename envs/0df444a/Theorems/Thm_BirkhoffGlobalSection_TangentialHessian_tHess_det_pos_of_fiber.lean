-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHess_det_pos_of_fiber
-- name    : BirkhoffGlobalSection.TangentialHessian.tHess_det_pos_of_fiber
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:43:18.319284+00:00
-- url     : https://prove2.me/theorems/302f5bf9-7f71-432a-9b40-089028c2a1c5
-- title:
--   Reduction of the tangential-Hessian determinant to the angle-free gate inequality
-- statement:
--   **Hypotheses.** Consider the Levi-Civita regularized Hamiltonian $K_{\mu,c}$ of the planar circular restricted three-body problem, with
--   $$0 \le \mu \le \tfrac12, \qquad \tfrac{21}{10} \le c \le \tfrac{21}{10} + 10^{-6}.$$
--   Let $s = (z_1, z_2, w_1, w_2)$ lie on the energy fiber $K_{\mu,c}(s) = 0$ with $2|z|^2 \le (3 - 2\mu)/5$, and let $r > 0$ with $r^2 = |2z^2 - 1|^2$. Let $T(s)$ be the symmetrized tangential Hessian in the quaternion frame $I\nabla K, J\nabla K, K\nabla K$.
--
--   **Conclusion.** If the fiber gate data satisfy
--   $$G > 0 \qquad\text{and}\qquad F\,(\beta_1^2 + \beta_2^2) < G^2,$$
--   then
--   $$\det T(s) > 0 .$$
--
--   This is the general structural reduction of the determinant clause of Joung–van Koert, Proposition 4.4. It combines:
--   - the quaternion-frame identity $\det T = |\nabla K|^4\, \nabla K^{\mathsf T}\operatorname{adj}(\operatorname{Hess}K)\nabla K$;
--   - the radial estimate of the previous clause, which gives $\nabla K \ne 0$;
--   - the block and fiber structure of $\operatorname{Hess} K$, which bounds the bordered form below on each fiber circle.
--
--   The remaining hypothesis involves no momentum angle: it depends on $(z, \mu, c, r)$ only. It is the gate inequality of Grisa, *Exact fiber elimination for the Levi–Civita convexity gates*, Zenodo 21270420 (2026), Theorem 3.7(b).
--
--   **Formalization note.** $G, F, \beta$ are `fibG`, `fibF`, `fibBeta1`, `fibBeta2`; $T(s)$ is `tHessR μ c r s`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (determinant clause); route of Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Theorem 3.7(b), and Grisa, companion paper, Zenodo 21376299 (2026), §5 (block-diagonal Hessian).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber

namespace BirkhoffGlobalSection.TangentialHessian

/-- **General reduction of the open leaf (D).** Under the hypotheses of `tHess_det_pos`, the
determinant of the tangential Hessian is positive as soon as the `φ`-free inequality
`fibG > 0 ∧ fibF · (fibBeta1² + fibBeta2²) < fibG²` holds (Grisa's Theorem 3.7(b)). -/
theorem tHess_det_pos_of_fiber (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5)
    (hG : 0 < fibG μ c r s)
    (hW : fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2) :
    0 < (tHessR μ c r s).det := by sorry

end BirkhoffGlobalSection.TangentialHessian
