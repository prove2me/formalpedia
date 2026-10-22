-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tangential_positive_of_tHess
-- name    : BirkhoffGlobalSection.TangentialHessian.tangential_positive_of_tHess
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:11.666022+00:00
-- url     : https://prove2.me/theorems/11985c78-5c8e-4d5c-95ae-f71e1918aed6
-- title:
--   Positive tangential Hessian of $K_{\mu,c}$ from the explicit $3\times3$ matrix
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $\nabla K$ and $\mathrm{THess}$ be the explicit gradient and the symmetrized $3\times3$ tangential Hessian `kGrad`, `tHess`. Let $s\in U$ with $\nabla K_{\mu,c}(s)\ne0$, and suppose that $\mathrm{THess}_{\mu,c}(s)$ is positive definite. Then for every nonzero $v\in\mathbb R^4$ with $DK_{\mu,c}(s)[v]=0$,
--
--   $$
--   D\big(x\mapsto DK_{\mu,c}(x)[v]\big)(s)[v]>0 .
--   $$
--
--   This is the pointwise version of the positive-tangential-Hessian clause of Proposition 4.4, expressed through the explicit matrix that Joung–van Koert certify numerically.
--
--   **Formalization Note.** The conclusion is exactly the pointwise condition inside the platform predicate `HasPositiveTangentialHessianOn`.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Section 2.3 and Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- Away from the second collision, `∇K ≠ 0` and positive definiteness of the explicit
tangential Hessian `tHess` give the tangential-Hessian condition at `s`. -/
theorem tangential_positive_of_tHess (μ c : ℝ) (s : Phase) (hs : s ∈ U)
    (hg : kGrad μ c s ≠ 0) (hQ : QuadPos (tHess μ c s))
    (v : Phase) (hv : v ≠ 0)
    (hker : fderiv ℝ (leviCivitaHamiltonian μ c) s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x v) s v := by sorry

end BirkhoffGlobalSection.TangentialHessian
