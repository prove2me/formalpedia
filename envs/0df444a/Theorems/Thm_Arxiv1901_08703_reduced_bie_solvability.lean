-- Prove2me | Theorems.Thm_Arxiv1901_08703_reduced_bie_solvability
-- name    : Arxiv1901_08703.reduced_bie_solvability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:00:23.018674+00:00
-- url     : https://prove2.me/theorems/d7aebca1-9453-512b-a8ba-21ef948c10f9
-- title:
--   Remark 2.9: the reduced integral equation $(I+B)\Phi=G$ on $L^2(\Gamma_R)\times L^2(\partial B_R^-)$
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support, $k>0$, and let $R>0$ be such that $\Gamma_p\subset B_R$. Let $B=(A_{ij})_{i,j=1,2}$ be the upper-left block of the operator $A$ of (2.15), acting on $L^2(\Gamma_R)\times L^2(\partial B_R^-)$. Assume that $k^2$ is not a Dirichlet eigenvalue of $-\Delta$ in $D_R^-$. Then:
--
--   1. $I+B$ is boundedly invertible on $L^2(\Gamma_R)\times L^2(\partial B_R^-)$;
--   2. for every $d\in\mathbb S^1_-$, if $\Phi=(\varphi_1,\varphi_2)^T$ solves $(I+B)\Phi=G$ with $G=(2(\partial u^i/\partial\nu+\partial u^r/\partial\nu)|_{\Gamma_R},0)^T$ (eq. (2.35)), then
--   $$u^s(x)=\int_{\Gamma_R}\Phi_k(x,y)\varphi_1(y)\,ds(y)+\int_{\partial B_R^-}\Phi_k(x,y)\varphi_2(y)\,ds(y)\tag{2.34}$$
--   solves the Neumann problem (NP), and its far-field pattern is
--   $$u^\infty(\hat x)=(S^\infty_{k,\Gamma_R}\varphi_1)(\hat x)+(S^\infty_{k,\partial B_R^-}\varphi_2)(\hat x).\tag{2.36}$$
--
--   **Formalization Note** "Boundedly invertible" is stated as follows: there is $C$ such that for every right-hand side $g$ the equation $(I+B)\Phi=g$ has exactly one solution, and $\|\Phi\|\le C\|g\|$. The product norm is the maximum of the two norms. The far-field pattern is asserted for the directions $\hat x\in\mathbb S^1_+$.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c009; Section 2, Remark 2.9, eqs. (2.34)-(2.36), PDF p. 14

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem reduced_bie_solvability (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ) (hh : IsLocalProfile h)
    (R : ℝ) (hR : PerturbationInBall h R)
    (hD : ¬ IsDirichletEigenvalue (DRminus h R) (k ^ 2)) :
    (∃ C : ℝ, ∀ g : Ysp h R,
      (∃! psi : Ysp h R, IsBSolution k h R psi ⇑g.1 ⇑g.2) ∧
      ∀ psi : Ysp h R, IsBSolution k h R psi ⇑g.1 ⇑g.2 → ‖psi‖ ≤ C * ‖g‖) ∧
    ∀ d : R2, IsLowerDir d → ∀ psi : Ysp h R, IsBSolution k h R psi (gData k d h) 0 →
      IsNPSolution k h (incData k d h) (slPotB k h R ⇑psi.1 ⇑psi.2) ∧
      HasFarFieldOn k (slPotB k h R ⇑psi.1 ⇑psi.2) (ffPotB k h R ⇑psi.1 ⇑psi.2) upperCircle := by sorry

end Arxiv1901_08703
