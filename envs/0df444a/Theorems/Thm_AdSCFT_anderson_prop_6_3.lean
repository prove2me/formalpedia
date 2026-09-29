-- Prove2me | Theorems.Thm_AdSCFT_anderson_prop_6_3
-- name    : AdSCFT.anderson_prop_6_3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:46:04.198421+00:00
-- url     : https://prove2.me/theorems/ebafab79-c8eb-4628-adda-90a80594ab77
-- title:
--   Proposition 6.3: $\rho^2 \le 4n(n-1)/|R_\gamma|$ for dS space-times
-- statement:
--   This is the analytic form of the de Sitter counterpart of the boundary-distance estimate: Anderson, *Geometric aspects of the AdS/CFT correspondence* ([arXiv:hep-th/0403087v2](https://arxiv.org/abs/hep-th/0403087)), §6, Proposition 6.3, estimate (6.16), proved independently by Andersson–Galloway.
--
--   Let $(S, g)$ be an $(n+1)$-dimensional globally hyperbolic space-time with compact Cauchy surface, $C^3$ conformally compact to the past, satisfying the strong energy and decay conditions $(\mathrm{Ric}_g - n g)(T, T) \ge 0$ and $|(\mathrm{Ric}_g - n g)(T,T)| = o(\rho^2)$ for timelike $T$, and let $\gamma$ be a representative of past conformal infinity with constant scalar curvature $R_\gamma$. Along the timelike geodesics orthogonal to $\mathcal I^-$ the Raychaudhuri equation gives, for $\varphi(\rho) = -\bar\Delta\rho/\rho$, the reversed focusing inequality (6.17)
--
--   $$\varphi'(\rho) \;\le\; -\frac{\rho\,\varphi(\rho)^2}{n},$$
--
--   while the initial-value identity (4.8) continues to hold, so $R_\gamma < 0$ forces $\varphi(0) < 0$.
--
--   The statement asserts that these data give the same bound with $|R_\gamma|$ in place of $R_\gamma$: if $n \ge 2$, $R_\gamma < 0$, $L \ge 0$, $\varphi$ satisfies the reversed inequality on all of $[0, L]$ and $(n-1)\varphi(0) = \tfrac12 R_\gamma$, then
--
--   $$L^2 \;\le\; \frac{4n(n-1)}{|R_\gamma|}.$$
--
--   Geometrically this says that no Cauchy surface $\Sigma_\rho$ exists for $\rho^2 > 4n(n-1)/|R_\gamma|$: every timelike geodesic is future incomplete and future conformal infinity is empty, which is the drastic form the role of the sign of $R_\gamma$ takes in the Lorentzian setting.
--
--   **Formalization Note** As for Theorem 4.1, the Raychaudhuri inequality and the initial value are hypotheses on a real function of the parameter $\rho$; the absolute value in the conclusion is the absolute value of the real number $R_\gamma$, which is negative by hypothesis.
-- source:
--   M. T. Anderson, Geometric aspects of the AdS/CFT correspondence, arXiv:hep-th/0403087v2, https://arxiv.org/abs/hep-th/0403087, p. 19, Section 6, Proposition 6.3, estimate (6.16) and inequality (6.17)

import Definitions.Def_AdSCFTFocusingProfiles

namespace AdSCFT

theorem anderson_prop_6_3 (n : ℕ) (hn : 2 ≤ n) (Rgamma L : ℝ) (hR : Rgamma < 0)
    (hL : 0 ≤ L) (phi phi' : ℝ → ℝ) (hprofile : FocusingProfileDS n L phi phi')
    (hinit : ((n : ℝ) - 1) * phi 0 = Rgamma / 2) :
    L ^ 2 ≤ 4 * n * ((n : ℝ) - 1) / |Rgamma| := by sorry

end AdSCFT
