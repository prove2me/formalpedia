-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_quadPos_tHess_leftCollisionPoint
-- name    : BirkhoffGlobalSection.TangentialHessian.quadPos_tHess_leftCollisionPoint
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:19.705987+00:00
-- url     : https://prove2.me/theorems/08364140-96d0-4f9b-9cef-01f005719ae8
-- title:
--   Tangential Hessian at the regularized collision point is positive definite
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $0\le\mu\le\tfrac12$ and $c\ge\tfrac{21}{10}$, and let $s_0=(0,0,\sqrt{1-\mu},0)$ be the regularized collision point over the primary at $(-\mu,0)$. Then the tangential Hessian $\mathrm{THess}_{\mu,c}(s_0)$ is positive definite:
--
--   $$
--   \sum_{i,j=1}^3a_ia_j\,\mathrm{THess}_{\mu,c}(s_0)_{ij}>0\qquad\text{for all }a\in\mathbb R^3\setminus\{0\}.
--   $$
--
--   At $s_0$ the matrix equals $(1-\mu)$ times the matrix $\begin{pmatrix}\kappa&-\mu\kappa&0\\-\mu\kappa&2(\tfrac12-\mu^3+(c+1)\mu^2)&0\\0&0&\kappa\end{pmatrix}$ of Lemma 4.3, where $\kappa=2c-\mu^2-2\mu$. The statement provides a base point for continuity and connectedness arguments along the energy component.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Lemma 4.3 (tangential Hessian at the collision point).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- At the regularized collision point `(0, 0, √(1-μ), 0)` the tangential Hessian is positive
definite (Joung--van Koert, Lemma 4.3). -/
theorem quadPos_tHess_leftCollisionPoint (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) :
    QuadPos (tHess μ c (leftCollisionPoint μ)) := by sorry

end BirkhoffGlobalSection.TangentialHessian
