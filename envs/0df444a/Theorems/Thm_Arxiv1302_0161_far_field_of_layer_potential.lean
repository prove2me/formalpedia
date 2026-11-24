-- Prove2me | Theorems.Thm_Arxiv1302_0161_far_field_of_layer_potential
-- name    : Arxiv1302_0161.far_field_of_layer_potential
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:25:38.881697+00:00
-- url     : https://prove2.me/theorems/c26569d5-5daf-4273-8e00-f06231b66384
-- title:
--   Remark 2.6: the far field pattern (2.8) of the combined layer potential
-- statement:
--   Let $k>0$, let $\eta\neq0$ be real, let $h_\Gamma\in C^2(\mathbb R)$ have compact support, let $R>0$ with $\Gamma_p\subset B_R$, and let $d\in S_-$. Let $\varphi\in C(\partial D_R^-)$ solve $P\varphi=g$, and let $u^s=\mathcal D_k\varphi-i\eta\mathcal S_k\varphi$. Define
--
--   $$u^\infty(\hat x)=\frac{e^{-i\pi/4}}{\sqrt{8\pi k}}\int_{\partial D_R^-}\big[k\,\nu(y)\cdot\hat x+\eta\big]e^{-ik\hat x\cdot y}\varphi(y)\,ds(y).$$
--
--   Then $u^\infty$ is the far field pattern of $u^s$ in every direction: there are $C$ and $\rho>0$ such that
--
--   $$\Big|u^s(x)-\frac{e^{ik|x|}}{\sqrt{|x|}}u^\infty(\hat x)\Big|\le\frac{C}{|x|^{3/2}}\qquad(|x|\ge\rho,\ \hat x=x/|x|).$$
--
--   Moreover, $\theta\mapsto u^\infty(\cos\theta,\sin\theta)$ is real-analytic, so $u^\infty$ is an analytic function on the unit circle $S$.
--
--   **Formalization Note** The asymptotic statement $u^s(x)=\frac{e^{ik|x|}}{\sqrt{|x|}}\big(u^\infty(\hat x)+O(1/|x|)\big)$, uniformly in $\hat x\in S$, is written with an explicit constant. Analyticity on $S$ is analyticity in the angle.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c008; Section 2, Remark 2.6, eq. (2.8), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem far_field_of_layer_potential (k : ℝ) (hk : 0 < k) (eta : ℝ) (heta : eta ≠ 0)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (d : R2) (hd : IsLowerDir d) (phi : R2 → ℂ) (hphi : ContinuousOn phi (bdry h R))
    (hP : ∀ x ∈ bdry h R, opP k eta h R phi x = gData k d h R x) :
    HasFarFieldOn k (combinedPot k eta h R phi) (farFieldFormula k eta h R phi)
      (Metric.sphere 0 1) ∧
    ∀ θ : ℝ, AnalyticAt ℝ
      (fun s : ℝ => farFieldFormula k eta h R phi (pt (Real.cos s) (Real.sin s))) θ := by sorry

end Arxiv1302_0161
