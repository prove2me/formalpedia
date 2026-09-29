-- Prove2me | Theorems.Thm_AdSCFT_anderson_thm_4_1
-- name    : AdSCFT.anderson_thm_4_1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:50:54.216618+00:00
-- url     : https://prove2.me/theorems/73ccc37b-063b-498e-9cc5-fcc9cefd4130
-- title:
--   Theorem 4.1: $\rho^2(x) \le 4n(n-1)/R_\gamma$ when $R_\gamma > 0$
-- statement:
--   This is the analytic form of the boundary-distance estimate of Anderson, *Geometric aspects of the AdS/CFT correspondence* ([arXiv:hep-th/0403087v2](https://arxiv.org/abs/hep-th/0403087)), §4, Theorem 4.1, estimate (4.2).
--
--   Let $g$ be a $C^3$ conformally compact metric on an $(n+1)$-manifold $M$ with $\mathrm{Ric}_g + n g \ge 0$ and $|\mathrm{Ric}_g + n g| = o(\rho^2)$, let $\partial_0 M$ be a boundary component with boundary metric $\gamma$ of constant scalar curvature $R_\gamma > 0$, and let $\rho$ be the geodesic defining function determined by $(\partial_0 M, \gamma)$. Anderson's Riccati comparison argument produces, along the $\bar g$-geodesics normal to $\partial_0 M$, the function $\varphi(\rho) = -\bar\Delta\rho/\rho$, which satisfies the focusing inequality (4.7)
--
--   $$\varphi'(\rho) \;\ge\; \frac{\rho\,\varphi(\rho)^2}{n}$$
--
--   and, by the Gauss equation (4.8), the initial condition $(n-1)\varphi(0) = \tfrac12 R_\gamma$.
--
--   The statement asserts that these two pieces of data already force the distance bound: if $n \ge 2$, $R_\gamma > 0$, $L \ge 0$, and $\varphi$ satisfies the focusing inequality on the whole interval $[0, L]$ with $(n-1)\varphi(0) = \tfrac12 R_\gamma$, then
--
--   $$L^2 \;\le\; \frac{4n(n-1)}{R_\gamma}.$$
--
--   Geometrically, $L$ is the $\bar g$-distance of a point of $M$ to $\partial_0 M$ along a normal geodesic, so the conclusion is exactly (4.2): every point of $M$ lies within $\bar g$-distance $\sqrt{4n(n-1)/R_\gamma}$ of the boundary. This is what makes $\partial M$ connected in the Witten–Yau theorem, and what rules out the formation of cusps in families of asymptotically hyperbolic Einstein metrics with uniformly positive boundary scalar curvature.
--
--   **Formalization Note** The focusing inequality and the initial value are taken as hypotheses on a real function $\varphi$ of the distance parameter, since Mathlib has no Ricci curvature of a Riemannian manifold; the statement formalizes the comparison step of the proof, not the derivation of (4.7) and (4.8) from the geometry. The hypothesis set is satisfiable — for example $\varphi \equiv c$ constant with $L = 0$ — so the statement is not vacuous, and the conclusion is an inequality on the length of the interval on which the profile exists.
-- source:
--   M. T. Anderson, Geometric aspects of the AdS/CFT correspondence, arXiv:hep-th/0403087v2, https://arxiv.org/abs/hep-th/0403087, p. 13, Section 4, Theorem 4.1, estimate (4.2)

import Definitions.Def_AdSCFTFocusingProfiles

namespace AdSCFT

theorem anderson_thm_4_1 (n : ℕ) (hn : 2 ≤ n) (Rgamma L : ℝ) (hR : 0 < Rgamma)
    (hL : 0 ≤ L) (phi phi' : ℝ → ℝ) (hprofile : FocusingProfileAH n L phi phi')
    (hinit : ((n : ℝ) - 1) * phi 0 = Rgamma / 2) :
    L ^ 2 ≤ 4 * n * ((n : ℝ) - 1) / Rgamma := by sorry

end AdSCFT
