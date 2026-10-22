-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHess_det_pos_mu_zero
-- name    : BirkhoffGlobalSection.TangentialHessian.tHess_det_pos_mu_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T17:30:58.897393+00:00
-- url     : https://prove2.me/theorems/365ae4aa-c072-48e6-af3c-c7c65acfc6d5
-- title:
--   Positive tangential Hessian determinant for the rotating Kepler problem (mu = 0)
-- statement:
--   Consider the Levi-Civita regularized Hamiltonian $K_{\mu,c}$ of the planar circular restricted three-body problem in the coordinates $s = (z_1, z_2, w_1, w_2)$, in the rotating-Kepler case $\mu = 0$, with $\tfrac{21}{10} \le c \le \tfrac{21}{10} + 10^{-6}$. Let $s$ lie on the level set $K_{0,c}(s) = 0$ with $2|z|^2 \le \tfrac35$, and let $r > 0$ with $r^2 = |2z^2 - 1|^2$. Let $T(s)$ be the symmetrized $3\times 3$ tangential Hessian of $K_{0,c}$ in the quaternion frame $I\nabla K, J\nabla K, K\nabla K$ (Joung–van Koert, Section 2.3). Then
--   $$\det T(s) > 0 .$$
--
--   This is the case $\mu = 0$ of the determinant inequality in Proposition 4.4 of Joung–van Koert, which they verified by computer for $0 \le \mu \le \tfrac12$. Here it is proved analytically, apart from a two-box certificate for a univariate polynomial inequality.
--
--   The proof has four steps:
--   1. The frame determinant equals $|\nabla K|^4$ times the bordered form $\nabla K^{\mathsf T}\operatorname{adj}(\operatorname{Hess}K)\,\nabla K$.
--   2. On the fiber, that form is a degree-two trigonometric polynomial in the momentum angle. This is the harmonic structure of Grisa, *Exact fiber elimination for the Levi–Civita convexity gates*, 2026.
--   3. At $\mu = 0$ its constant term and harmonic amplitudes depend on $|z|^2$ alone.
--   4. Positivity therefore reduces to two univariate polynomial inequalities on $0 \le |z|^2 \le \tfrac{3}{10}$.
--
--   For a different, Ligon–Schaaf–Levi-Civita embedding, convexity of the rotating Kepler problem was proved by Frauenfelder–van Koert–Zhao (arXiv:1605.06981). The present statement concerns the plain Levi-Civita embedding used in Proposition 4.4.
--
--   **Formalization note.** The radius $r$ enters as a free real with $r > 0$ and $r^2$ equal to the squared distance to the second collision, as in the other statements of this family. At $\mu = 0$ it does not enter the Hessian.
-- source:
--   The mu = 0 case of the open leaf tHess_det_pos behind Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4; route follows Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Theorem 3.7(b).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- **(D) at `μ = 0`** (rotating Kepler problem): the tangential Hessian has positive
determinant on the fiber. -/
theorem tHess_det_pos_mu_zero (c r : ℝ) (s : Phase)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hK : pP 0 c s - 0 * (zNormSq s / r) = 0)
    (hz : 2 * zNormSq s ≤ 3 / 5) :
    0 < (tHessR 0 c r s).det := by sorry

end BirkhoffGlobalSection.TangentialHessian
