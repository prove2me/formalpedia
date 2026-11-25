-- Prove2me | Theorems.Thm_Arxiv1901_08703_bie_rhs_mem_and_operator_bounded
-- name    : Arxiv1901_08703.bie_rhs_mem_and_operator_bounded
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:35:38.425226+00:00
-- url     : https://prove2.me/theorems/a5fb60e2-c525-42b1-a1ea-20b16172b166
-- title:
--   Eqs. (2.14)-(2.16): $G\in X$ and $A$ is a bounded linear operator on $X$
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support, $k>0$, $\rho>0$, let $R>0$ be such that the local perturbation of $\Gamma$ lies in $B_R$, and let $\tilde D$ be an auxiliary domain with $C^2$ boundary $\tilde\Gamma$ and $\overline{\tilde D}\subset D_R^-$. Let $X=L^2(\Gamma_R)\times L^2(\partial B_R^-)\times H^{-1/2}(\tilde\Gamma)$, let $A=(A_{ij})_{3\times3}$ be the operator of eq. (2.15),
--   $$A_{1j}=-2K'_{k,I_j\to\Gamma_R},\quad A_{2j}=-2\big(K'_{k,I_j\to\partial B_R^-}-K'^{,re}_{k,I_j\to\partial B_R^-}\big),\quad A_{3j}=-2\big(K'_{k,I_j\to\tilde\Gamma}+i\rho S_{k,I_j\to\tilde\Gamma}\big),$$
--   with $(I_1,I_2,I_3)=(\Gamma_R,\partial B_R^-,\tilde\Gamma)$, and let $G=\big(2(\partial u^i/\partial\nu+\partial u^r/\partial\nu)|_{\Gamma_R},0,0\big)^T$ (eq. (2.16)). Then:
--
--   1. $G\in X$ for every incident direction $d\in\mathbb S^1_-$;
--   2. $A$ is a bounded linear operator on $X$: there is a bounded linear map $T:X\to X$ whose components agree with the three rows of $A$ (almost everywhere on $\Gamma_R$ and on $\partial B_R^-$, and as elements of $H^{-1/2}(\tilde\Gamma)$).
--
--   **Formalization Note** The paper derives (2.14) from the ansatz (2.10) and the boundary conditions (2.11)-(2.13), and then asserts that $G\in X$ and that $A$ is bounded on $X$. Only these two assertions are stated. The converse direction of the derivation is Lemma 2.3. An element of $H^{-1/2}(\tilde\Gamma)$ is represented by $b\in\ell^2(\mathbb Z)$ through the Fourier coefficients $a_n=(1+n^2)^{1/4}b_n$ of $s\mapsto\varphi_3(z(s))|z'(s)|$. The third row of $A$ is given by its Fourier coefficients, and $A_{33}$ acts on $(a_n)$ as the matrix described in the definitions.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c019; Section 2, eqs. (2.10)-(2.16) and the sentence after (2.16), PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem bie_rhs_mem_and_operator_bounded (k : ℝ) (hk : 0 < k) (ρ : ℝ) (hρ : 0 < ρ)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (aux : AuxDomain h R) :
    (∀ d : R2, IsLowerDir d → MemLp (gData k d h) 2 (muG h R)) ∧
    ∃ T : Xsp h R →L[ℂ] Xsp h R, ∀ sol : Xsp h R,
      ⇑(T sol).1 =ᵐ[muG h R] opA1 k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) ∧
      ⇑(T sol).2.1 =ᵐ[muB R] opA2 k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) ∧
      ∀ m : ℤ, hmhCoeff (T sol).2.2 m = opA3 k ρ h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) m := by sorry

end Arxiv1901_08703
