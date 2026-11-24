-- Prove2me | Theorems.Thm_Arxiv1302_0161_parameterised_bie
-- name    : Arxiv1302_0161.parameterised_bie
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:26:10.448662+00:00
-- url     : https://prove2.me/theorems/b404cd19-309f-4d56-9298-cc39ac5d331a
-- title:
--   Section 3: the integral equation $P\varphi=g$ in the graded-mesh parameterisation
-- statement:
--   Let $k>0$, let $\eta\neq0$ be real, let $h_\Gamma\in C^2(\mathbb R)$ have compact support, and let $R>0$ with $\Gamma_p\subset B_R$. Let $\omega$ be Kress's grading function with $p=4$, and let $x(s)$, $0\le s\le2\pi$, be the parameterisation of $\partial D_R^-$ in Section 3. Then:
--
--   1. $\omega$ is strictly increasing on $[0,2\pi]$, with $\omega(0)=0$ and $\omega(\pi)=\pi$, and $\omega$ is differentiable at $0$ and at $\pi$ with $\omega'(0)=\omega'(\pi)=0$;
--   2. $x$ maps $(0,2\pi]$ onto $\partial D_R^-$;
--   3. for every $\varphi\in C(\partial D_R^-)$, writing $I(z)=\int_0^{2\pi}\Big[\frac{\partial\Phi_k(z,x(s))}{\partial\nu(x(s))}-i\eta\Phi_k(z,x(s))\Big]\varphi(x(s))\,|x'(s)|\,ds$,
--
--   $$P\varphi(x(t))=\begin{cases}\varphi(x(t))+2\,I(x(t)),&0<t<\pi,\\[2pt]\tfrac12\varphi(x(t))+I(x(t))+I(x^{re}(t)),&\pi\le t\le2\pi.\end{cases}$$
--
--   By 2, the equation $P\varphi=g$ on $\partial D_R^-$ therefore amounts to $P\varphi(x(t))=g(x(t))$ for $0<t\le2\pi$ in the parameterised form of 3; this consequence is not itself part of the formal statement. This is the form discretised by the Nyström method of Section 3.
--
--   **Formalization Note** The printed formula (PDF p. 10) omits the density $\varphi(x(s))$ under both integrals. It is inserted here, as the paper's own discrete system and far-field quadrature require. The value $t=0$ is not in the paper's case split. The corner $x_B=x(0)$ is covered as $t=2\pi$.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c013 (supersedes c009); Section 3, parameterisation of the boundary and the parameterised equation following it, PDF pp. 9-10

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem parameterised_bie (k : ℝ) (hk : 0 < k) (eta : ℝ) (heta : eta ≠ 0)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (phi : R2 → ℂ) (hphi : ContinuousOn phi (bdry h R)) :
    StrictMonoOn (kressOmega 4) (Set.Icc 0 (2 * Real.pi)) ∧
    kressOmega 4 0 = 0 ∧ kressOmega 4 Real.pi = Real.pi ∧
    HasDerivAt (kressOmega 4) 0 0 ∧ HasDerivAt (kressOmega 4) 0 Real.pi ∧
    gradedPt R h '' Set.Ioc 0 (2 * Real.pi) = bdry h R ∧
    (∀ t ∈ Set.Ioo 0 Real.pi,
      opP k eta h R phi (gradedPt R h t) =
        phi (gradedPt R h t) + 2 * paramInt k eta R h phi (gradedPt R h t)) ∧
    ∀ t ∈ Set.Icc Real.pi (2 * Real.pi),
      opP k eta h R phi (gradedPt R h t) =
        phi (gradedPt R h t) / 2 + paramInt k eta R h phi (gradedPt R h t) +
          paramInt k eta R h phi (refl (gradedPt R h t)) := by sorry

end Arxiv1302_0161
