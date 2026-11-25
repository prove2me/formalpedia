-- Prove2me | Theorems.Thm_Arxiv1901_08703_bie_unique_solvability
-- name    : Arxiv1901_08703.bie_unique_solvability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:48:11.912303+00:00
-- url     : https://prove2.me/theorems/ca7c5121-2fa2-4ec2-8d13-acf7f2b933bc
-- title:
--   Theorem 2.4: unique solvability of the integral equation $(I+A)\Phi=G$ in $X$
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support, $k>0$, $\rho>0$, let $R>0$ be such that $\Gamma_p\subset B_R$, and let $\tilde D$ be an auxiliary domain with $C^2$ boundary $\tilde\Gamma$ and $\overline{\tilde D}\subset D_R^-$. Assume that $k^2$ is not a Dirichlet eigenvalue of $-\Delta$ in $\tilde D$. Then there is a constant $C$ such that, for every incident direction $d\in\mathbb S^1_-$, the integral equation $(I+A)\Phi=G$ with $A$, $G$ of (2.15), (2.16) has a unique solution $\Phi=(\varphi_1,\varphi_2,\varphi_3)^T\in X=L^2(\Gamma_R)\times L^2(\partial B_R^-)\times H^{-1/2}(\tilde\Gamma)$, and
--   $$\|\varphi_1\|_{L^2(\Gamma_R)}+\|\varphi_2\|_{L^2(\partial B_R^-)}+\|\varphi_3\|_{H^{-1/2}(\tilde\Gamma)}\le C\left\|\frac{\partial u^i}{\partial\nu}+\frac{\partial u^r}{\partial\nu}\right\|_{L^2(\Gamma)}.\tag{2.17}$$
--
--   **Formalization Note** The norm on $X$ is the maximum of the three norms. The $H^{-1/2}(\tilde\Gamma)$ norm is the $\ell^2$ norm of $b_n=(1+n^2)^{-1/4}a_n$, where $(a_n)$ are the Fourier coefficients of $s\mapsto\varphi_3(z(s))|z'(s)|$. These norms are equivalent to the paper's, so only the value of $C$ changes. The paper does not say what $C$ depends on. The statement takes $C$ independent of the incident direction $d$, which is what the proof gives: $C=2\|(I+A)^{-1}\|$. Dirichlet eigenvalues are taken in the classical sense ($u\in C^2(\tilde D)\cap C(\overline{\tilde D})$), which agrees with the $H^1_0$ sense for a $C^2$ domain.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c004; Section 2, Theorem 2.4, eqs. (2.14)-(2.17), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem bie_unique_solvability (k : ℝ) (hk : 0 < k) (ρ : ℝ) (hρ : 0 < ρ)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (aux : AuxDomain h R) (hD : ¬ IsDirichletEigenvalue aux.D (k ^ 2)) :
    ∃ C : ℝ, ∀ d : R2, IsLowerDir d →
      (∃! sol : Xsp h R, IsBIESolution k ρ h R aux d sol) ∧
      ∀ sol : Xsp h R, IsBIESolution k ρ h R aux d sol →
        ‖sol‖ ≤ C * l2Gam h (incData k d h) := by sorry

end Arxiv1901_08703
