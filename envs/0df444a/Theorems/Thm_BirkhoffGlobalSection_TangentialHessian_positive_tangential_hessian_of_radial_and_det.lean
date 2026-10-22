-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_positive_tangential_hessian_of_radial_and_det
-- name    : BirkhoffGlobalSection.TangentialHessian.positive_tangential_hessian_of_radial_and_det
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:27.672301+00:00
-- url     : https://prove2.me/theorems/7f83afb7-9c7f-4a5d-9935-cd10f847910f
-- title:
--   Proposition 4.4 (positive tangential Hessian), conditional on radial and determinant positivity
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $0\le\mu\le\tfrac12$ and $c\ge\tfrac{21}{10}$, and let $\Sigma_{\mu,c}$ be the left energy component. Assume that on $\Sigma_{\mu,c}$
--
--   1. the radial derivative is positive, $\sum_i s_i\nabla K_{\mu,c}(s)_i>0$, and
--   2. the tangential Hessian has positive determinant, $\det\mathrm{THess}_{\mu,c}(s)>0$.
--
--   Then $K_{\mu,c}$ is $C^2$ on $\Sigma_{\mu,c}$ and has positive tangential Hessian there: for every $s\in\Sigma_{\mu,c}$ and every nonzero $v$ with $DK_{\mu,c}(s)[v]=0$,
--
--   $$
--   D\big(x\mapsto DK_{\mu,c}(x)[v]\big)(s)[v]>0 .
--   $$
--
--   This reduces the positive-tangential-Hessian clause of Proposition 4.4 to two explicit inequalities on the component, which are the quantities certified numerically in the source. Compared with the mission statement `positive_tangential_hessian`, it holds for every $c\ge\frac{21}{10}$.
--
--   **Formalization Note.** The conclusion is the platform predicate `HasPositiveTangentialHessianOn`.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- Joung--van Koert, Proposition 4.4 (positive-tangential-Hessian clause), conditional on
positivity of the radial derivative and of the tangential-Hessian determinant on the left
energy component, for all `c ≥ 21/10`. -/
theorem positive_tangential_hessian_of_radial_and_det (μ c : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc0 : 21 / 10 ≤ c)
    (hrad : ∀ s ∈ leftEnergyComponent μ c, 0 < ∑ i, s i * kGrad μ c s i)
    (hdet : ∀ s ∈ leftEnergyComponent μ c, 0 < (tHess μ c s).det) :
    HasPositiveTangentialHessianOn (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection.TangentialHessian
