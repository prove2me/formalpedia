-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_quadPos_tHess_of_det_pos
-- name    : BirkhoffGlobalSection.TangentialHessian.quadPos_tHess_of_det_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:14.411212+00:00
-- url     : https://prove2.me/theorems/b17c50ab-dad0-41c3-8aab-d40b9cb57bc7
-- title:
--   Positive determinant of $\mathrm{THess}$ on the energy component implies positive definiteness
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $0\le\mu\le\tfrac12$ and $c\ge\tfrac{21}{10}$, and let $\Sigma_{\mu,c}$ be the left energy component. Suppose that the symmetrized tangential Hessian has positive determinant everywhere on it:
--
--   $$
--   \det\mathrm{THess}_{\mu,c}(s)>0\qquad\text{for all }s\in\Sigma_{\mu,c}.
--   $$
--
--   Then $\mathrm{THess}_{\mu,c}(s)$ is positive definite for every $s\in\Sigma_{\mu,c}$.
--
--   This isolates the purely numerical content of the positive-tangential-Hessian clause of Proposition 4.4. Once the determinant is known to be positive along the component, definiteness propagates from the collision point by connectedness.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 and Lemma 4.3.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- If the tangential Hessian has positive determinant at every point of the left energy
component, then it is positive definite at every point of the component. -/
theorem quadPos_tHess_of_det_pos (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c)
    (hdet : ∀ s ∈ leftEnergyComponent μ c, 0 < (tHess μ c s).det) :
    ∀ s ∈ leftEnergyComponent μ c, QuadPos (tHess μ c s) := by sorry

end BirkhoffGlobalSection.TangentialHessian
