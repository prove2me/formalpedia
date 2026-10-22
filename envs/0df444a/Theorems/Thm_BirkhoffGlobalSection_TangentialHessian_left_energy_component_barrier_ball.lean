-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_left_energy_component_barrier_ball
-- name    : BirkhoffGlobalSection.TangentialHessian.left_energy_component_barrier_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:13.206992+00:00
-- url     : https://prove2.me/theorems/8f7a5482-d0bb-4c4d-851a-68f9a2386b91
-- title:
--   The left energy component lies inside $|q+\mu|<(3-2\mu)/5$
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $0\le\mu\le\tfrac12$ and $c\ge\tfrac{21}{10}$, and let $\Sigma_{\mu,c}$ be the left energy component: the connected component of $\{K_{\mu,c}=0,\ D>0\}$ through the collision point $(0,0,\sqrt{1-\mu},0)$. Then every $s\in\Sigma_{\mu,c}$ satisfies
--
--   $$
--   2\,(z_1^2+z_2^2)\;<\;\frac{3-2\mu}{5},\qquad\text{equivalently}\qquad \lvert q+\mu\rvert<\frac{3-2\mu}{5}.
--   $$
--
--   This is the containment that the computer-assisted proof of Proposition 4.4 uses to discard boxes with $2\lvert z\rvert^2>(3-2\mu)/5$. Lemma 4.1 of the source gives the non-strict bound $d_{\mu,c}\le\frac{3-2\mu}{5}$ for the distance along the axis between the primaries. The statement here is strict, holds at every point of the component, and does not rely on reducing to that axis. It is derived from the all-angle barrier `BirkhoffGlobalSection.lc_barrier_positive`.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Lemma 4.1 and the box test in the proof of Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- The left energy component lies strictly inside the ball `2|z|² < (3 - 2μ)/5`
(i.e. `|q + μ| < (3 - 2μ)/5`). -/
theorem left_energy_component_barrier_ball (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) :
    ∀ s ∈ leftEnergyComponent μ c, 2 * zNormSq s < (3 - 2 * μ) / 5 := by sorry

end BirkhoffGlobalSection.TangentialHessian
