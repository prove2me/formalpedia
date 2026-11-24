-- Prove2me | Theorems.Thm_Arxiv1302_0161_far_field_operator_frechet_derivative
-- name    : Arxiv1302_0161.far_field_operator_frechet_derivative
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:27:16.690772+00:00
-- url     : https://prove2.me/theorems/d709ea37-e05e-4fb7-9c21-ec838cf802e6
-- title:
--   Theorem 4.2: Fréchet differentiability of the far field operator $F_d$
-- statement:
--   Let $k>0$, let $h_\Gamma\in C^2(\mathbb R)$ have compact support, let $R>0$ with $\Gamma_p\subset B_R$, and let $d\in S_-$. For a profile $h$, let $F_d(h)\in L^2(S_+)$ be the far field pattern on $S_+$ of the solution of (DP) for the surface $\{x_2=h(x_1)\}$ with $f=-(u^i+u^r)$. Let $u=u^i+u^r+u^s$ be the total field for $h_\Gamma$. For $\Delta h\in C^2_{0,R}(\mathbb R)$, let $u'$ solve (DP) for $h_\Gamma$ with boundary data
--
--   $$f=-(\nu_2\,\Delta h)\,\frac{\partial u}{\partial\nu}\quad\text{on }\Gamma,$$
--
--   where $\nu$ is the unit normal on $\Gamma$ directed into $D_+$. Let $F'_d(h_\Gamma,\Delta h)=u'_\infty$ be the far field pattern of $u'$. Then:
--
--   1. $\Delta h\mapsto F'_d(h_\Gamma,\Delta h)$ is linear;
--   2. it is bounded: $\|F'_d(h_\Gamma,\Delta h)\|_{L^2(S_+)}\le C\|\Delta h\|_{C^2(\mathbb R)}$;
--   3. $F_d$ is Fréchet differentiable at $h_\Gamma$ with derivative $F'_d(h_\Gamma,\cdot)$:
--
--   $$\|F_d(h_\Gamma+\Delta h)-F_d(h_\Gamma)-F'_d(h_\Gamma,\Delta h)\|_{L^2(S_+)}=o(\|\Delta h\|_{C^2(\mathbb R)})\quad(\|\Delta h\|_{C^2}\to0).$$
--
--   **Formalization Note** The solutions and their far fields enter as given functions of $\Delta h$ that satisfy (DP) and the far-field asymptotics. By Theorem 2.5 these solutions exist and are unique. The normal derivative $\partial u/\partial\nu$ is the one-sided derivative along $\nu$ from $D_+$. $\|\cdot\|_{C^2}$ is $\sup|\Delta h|+\sup|\Delta h'|+\sup|\Delta h''|$.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c011; Section 4, eq. (4.1), definition of Fréchet differentiability and Theorem 4.2, PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem far_field_operator_frechet_derivative (k : ℝ) (hk : 0 < k)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (d : R2) (hd : IsLowerDir d)
    (us : R2 → ℂ) (hus : IsDPSolution k h (incData k d) us)
    (Fs : R2 → ℂ) (hFs : HasFarFieldOn k us Fs upperCircle)
    (U : (ℝ → ℝ) → R2 → ℂ) (hU : ∀ dh ∈ C20R R, IsDPSolution k (h + dh) (incData k d) (U dh))
    (FU : (ℝ → ℝ) → R2 → ℂ) (hFU : ∀ dh ∈ C20R R, HasFarFieldOn k (U dh) (FU dh) upperCircle)
    (V : (ℝ → ℝ) → R2 → ℂ)
    (hV : ∀ dh ∈ C20R R, IsDPSolution k h (domainDerivData k d h us dh) (V dh))
    (FV : (ℝ → ℝ) → R2 → ℂ) (hFV : ∀ dh ∈ C20R R, HasFarFieldOn k (V dh) (FV dh) upperCircle) :
    (∀ dh1 ∈ C20R R, ∀ dh2 ∈ C20R R, ∀ a b : ℝ, ∀ xhat ∈ upperCircle,
      FV (a • dh1 + b • dh2) xhat = (a : ℂ) * FV dh1 xhat + (b : ℂ) * FV dh2 xhat) ∧
    (∃ C : ℝ, ∀ dh ∈ C20R R, l2NormUpper (FV dh) ≤ C * c2Norm dh) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ dh ∈ C20R R, c2Norm dh < δ →
      l2NormUpper (fun xhat => FU dh xhat - Fs xhat - FV dh xhat) ≤ ε * c2Norm dh := by sorry

end Arxiv1302_0161
