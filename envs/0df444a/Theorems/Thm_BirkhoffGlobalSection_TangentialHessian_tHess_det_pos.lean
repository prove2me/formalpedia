-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHess_det_pos
-- name    : BirkhoffGlobalSection.TangentialHessian.tHess_det_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T18:08:04.623985+00:00
-- url     : https://prove2.me/theorems/817a8bf0-cdbf-4da7-a4b7-6019f82ffbb3
-- title:
--   Positive determinant of the tangential Hessian on the energy surface
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $0\le\mu\le\tfrac12$ and $\tfrac{21}{10}\le c\le\tfrac{21}{10}+10^{-6}$. Let $s=(z,w)$ and $r>0$ satisfy
--
--   $$
--   r^2=D(s),\qquad P(s)-\mu\,\frac{Z}{r}=0,\qquad 2Z\le\frac{3-2\mu}{5},\qquad w_1^2+w_2^2\le4 .
--   $$
--
--   The first two conditions say that $s$ lies on the zero level $K_{\mu,c}=0$ with $r=\lvert 2z^2-1\rvert$. Then the symmetrized tangential Hessian in the frame $I\nabla K,J\nabla K,K\nabla K$ (`tHessR`, computed with this $r$) has positive determinant:
--
--   $$
--   \det\mathrm{THess}_{\mu,c}(s)>0 .
--   $$
--
--   This is the numerical core (D) of the positive-tangential-Hessian clause of Proposition 4.4. Together with [quadPos_tHess_of_det_pos](p2m:theorem/b17c50ab-dad0-41c3-8aab-d40b9cb57bc7), it yields positive definiteness of $\mathrm{THess}$ on the whole left energy component. Sampling suggests a minimum of about $0.21$, attained near $\mu=\frac12$, $z\approx(0,0.315)$. A useful identity for certification is $\det\mathrm{THess}=\lvert g\rvert^4\,g^{\mathsf T}\operatorname{adj}(\nabla^2K)\,g$ with $g=\nabla K$.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (positive definiteness of THess, verified there by interval arithmetic).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- On the zero level inside the barrier ball (with `r = |2z² - 1|` and the a priori bound
`|w|² ≤ 4`), the tangential Hessian in the frame `I∇K, J∇K, K∇K` has positive determinant. -/
theorem tHess_det_pos (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5) (hw : wNormSq s ≤ 4) :
    0 < (tHessR μ c r s).det := by sorry

end BirkhoffGlobalSection.TangentialHessian
