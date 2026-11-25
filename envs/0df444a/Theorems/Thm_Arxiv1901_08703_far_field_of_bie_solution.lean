-- Prove2me | Theorems.Thm_Arxiv1901_08703_far_field_of_bie_solution
-- name    : Arxiv1901_08703.far_field_of_bie_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:53:54.286333+00:00
-- url     : https://prove2.me/theorems/d8cc5323-6568-4b29-a6d5-31171209f650
-- title:
--   Remark 2.8: the far-field pattern $u^\infty=S^\infty\Phi$ of the solution of (NP)
-- statement:
--   Under the hypotheses of Theorem 2.4, let $d\in\mathbb S^1_-$ and let $\Phi=(\varphi_1,\varphi_2,\varphi_3)^T\in X$ be the solution of $(I+A)\Phi=G$. Then the solution $u^s$ of (NP) satisfies
--   $$u^s(x;d)=\frac{e^{ik|x|}}{\sqrt{|x|}}\left(u^\infty(\hat x;d)+O\Big(\frac1{|x|}\Big)\right),\qquad|x|\to\infty,$$
--   uniformly for $\hat x\in\mathbb S^1_+$, with far-field pattern
--   $$u^\infty(\hat x)=S^\infty\Phi:=(S^\infty_{k,\Gamma_R}\varphi_1)(\hat x)+(S^\infty_{k,\partial B_R^-}\varphi_2)(\hat x)+(S^\infty_{k,\tilde\Gamma}\varphi_3)(\hat x),\tag{2.33}$$
--   where $(S^\infty_{k,I}\varphi)(\hat x)=\frac{e^{i\pi/4}}{\sqrt{8\pi k}}\int_Ie^{-ik\hat x\cdot y}\varphi(y)\,ds(y)$ (eq. (2.5)). The function $S^\infty\Phi$ is analytic on the unit circle $\mathbb S^1$.
--
--   **Formalization Note** Analyticity on $\mathbb S^1$ is stated as real analyticity of $\theta\mapsto(S^\infty\Phi)(\cos\theta,\sin\theta)$ on $\mathbb R$. The asymptotics are stated for every solution of (NP) with this data; by Theorem 2.7 there is exactly one.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c021; Section 2, Remark 2.8, eqs. (2.5), (2.33), PDF p. 14

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem far_field_of_bie_solution (k : ℝ) (hk : 0 < k) (ρ : ℝ) (hρ : 0 < ρ)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (aux : AuxDomain h R) (hD : ¬ IsDirichletEigenvalue aux.D (k ^ 2))
    (d : R2) (hd : IsLowerDir d) (sol : Xsp h R) (hsol : IsBIESolution k ρ h R aux d sol) :
    (∀ u : R2 → ℂ, IsNPSolution k h (incData k d h) u →
      HasFarFieldOn k u (ffPot k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2)) upperCircle) ∧
    AnalyticOnNhd ℝ (fun θ : ℝ =>
      ffPot k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) (pt (Real.cos θ) (Real.sin θ)))
      Set.univ := by sorry

end Arxiv1901_08703
