-- Prove2me | Theorems.Thm_Arxiv1507_03491_impedance_local_integral_equation
-- name    : Arxiv1507_03491.impedance_local_integral_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:13:29.521261+00:00
-- url     : https://prove2.me/theorems/5fae1ce0-a80c-4595-9df7-71a1f05c149a
-- title:
--   Eq. (3.9): the impedance condition on $\Gamma_0$ for $S_{\Gamma_0}[\sigma]$ is the local integral equation
-- statement:
--   Let $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, $\operatorname{Re}\alpha\ge0$ and $M_0>0$. Let $\sigma$ be continuous on $[-M_0,M_0]$ and let $u_1^s=S_{\Gamma_0}[\sigma]$ be its single-layer potential (3.7). Let $g$ be any function on $\Gamma$ and $x\in\Gamma_0$. Then the impedance condition of (3.3) holds for $u_1^s$ at $(x,0)$, in the sense of limits from the upper half-plane,
--
--   $$\lim_{y\to0^+}\Big(\frac{\partial u_1^s}{\partial y}(x,y)+ik\alpha\,u_1^s(x,y)\Big)=g(x),$$
--
--   if and only if the local integral equation (3.9) holds at $x$:
--
--   $$-\tfrac12\sigma(x)+ik\alpha\,S_{\Gamma_0}[\sigma](x,0)=g(x).$$
--
--   The local equation is what the hybrid scheme solves for the impedance half-space.
--
--   **Formalization Note** The paper's derivation ("standard jump conditions") is stated as this equivalence. It holds because the limit on the left exists and equals $-\tfrac12\sigma(x)+ik\alpha S_{\Gamma_0}[\sigma](x,0)$. The density class is the paper's $\sigma\in C(\Gamma_0)$, read as continuity on the closed segment.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c007; Section 3, eqs. (3.3)–(3.4), PDF p. 9, and eqs. (3.7), (3.9), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem impedance_local_integral_equation (k alpha : ℂ) (hk : 0 < k.re) (hk' : 0 ≤ k.im)
    (halpha : 0 ≤ alpha.re) (M0 : ℝ) (hM0 : 0 < M0) (sigma : ℝ → ℂ)
    (hsigma : ContinuousOn sigma (Icc (-M0) M0)) (g : ℝ → ℂ) (x : ℝ) (hx : x ∈ Ioo (-M0) M0) :
    Tendsto (fun y : ℝ => deriv (fun t : ℝ => singleLayer k M0 sigma x t) y +
        Complex.I * k * alpha * singleLayer k M0 sigma x y) (𝓝[>] 0) (𝓝 (g x)) ↔
      -(1 / 2) * sigma x + Complex.I * k * alpha * singleLayer k M0 sigma x 0 = g x := by sorry

end Arxiv1507_03491
