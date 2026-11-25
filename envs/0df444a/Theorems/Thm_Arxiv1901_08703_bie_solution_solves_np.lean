-- Prove2me | Theorems.Thm_Arxiv1901_08703_bie_solution_solves_np
-- name    : Arxiv1901_08703.bie_solution_solves_np
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:38:01.616517+00:00
-- url     : https://prove2.me/theorems/4b6aac9f-1df5-4036-acac-dbfe0a82e58c
-- title:
--   Lemma 2.3: a solution of $(I+A)\Phi=G$ gives the solution of (NP)
-- statement:
--   Under the standing assumptions of Section 2 ($h\in C^2(\mathbb R)$ with compact support, $k>0$, $\rho>0$, $\Gamma_p\subset B_R$, and $\tilde D$ with $C^2$ boundary and $\overline{\tilde D}\subset D_R^-$), let $d\in\mathbb S^1_-$. Suppose $\Phi=(\varphi_1,\varphi_2,\varphi_3)^T\in X$ solves the boundary integral equation $(I+A)\Phi=G$ of (2.14)-(2.16), and let
--   $$u^s(x)=\int_{\Gamma_R}\Phi_k(x,y)\varphi_1(y)\,ds(y)+\int_{\partial B_R^-}\Phi_k(x,y)\varphi_2(y)\,ds(y)+\int_{\tilde\Gamma}\Phi_k(x,y)\varphi_3(y)\,ds(y)$$
--   (eq. (2.10)). Then $u^s\in H^1_{loc}(\mathbb R^2\setminus\overline{D_R^-})$, and $u^s$ solves the Neumann problem (NP) with data $f=-(\partial u^i/\partial\nu+\partial u^r/\partial\nu)$.
--
--   **Formalization Note** $u^s\in H^1_{loc}(\mathbb R^2\setminus\overline{D_R^-})$ means $\int_{B_\rho\setminus\overline{D_R^-}}(|u^s|^2+|\nabla u^s|^2)\,dx<\infty$ for every $\rho$. The integral over $\tilde\Gamma$ against $\varphi_3\in H^{-1/2}(\tilde\Gamma)$ is $\sum_na_n\int_0^{2\pi}\Phi_k(x,z(s))e^{ins}\,ds$.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c003; Section 2, Lemma 2.3, eqs. (2.10), (2.14)-(2.16), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem bie_solution_solves_np (k : ℝ) (hk : 0 < k) (ρ : ℝ) (hρ : 0 < ρ)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (aux : AuxDomain h R) (d : R2) (hd : IsLowerDir d) (sol : Xsp h R)
    (hsol : IsBIESolution k ρ h R aux d sol) :
    IsH1Loc (closure (DRminus h R))ᶜ (slPot k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2)) ∧
    IsNPSolution k h (incData k d h) (slPot k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2)) := by sorry

end Arxiv1901_08703
