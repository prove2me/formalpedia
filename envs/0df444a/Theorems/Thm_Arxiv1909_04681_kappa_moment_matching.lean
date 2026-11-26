-- Prove2me | Theorems.Thm_Arxiv1909_04681_kappa_moment_matching
-- name    : Arxiv1909_04681.kappa_moment_matching
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:48:30.483394+00:00
-- url     : https://prove2.me/theorems/f451ffde-4397-4a6f-b95c-cc463b476372
-- title:
--   Eq. (13): the moment-matched concentration parameter $\kappa(\mathrm{SNR})$
-- statement:
--   Let $V>0$ and $\sigma>0$, write $\mathrm{SNR}=V/\sigma$, and let $P$ be the single-baseline phase distribution of eq. (1). Write $\mathrm{vM}(0,\kappa,\cdot)$ for the von Mises density with location $0$.
--
--   1. (Eq. 4.) $P(\phi)=P_0+P_2\phi^2+O(\phi^3)$ as $\phi\to0$, with $P_0=P(0)$ and $P_2=P''(0)/2$.
--   2. (Eq. 7.) $$\frac{P_2}{P_0}=\frac{\mathrm{SNR}}{2\big\{\sqrt{2\pi}\,\mathrm{SNR}\,e^{\mathrm{SNR}^2/2}[\operatorname{Erf}(\mathrm{SNR}/\sqrt2)+1]+2\big\}}\Big\{\sqrt{2\pi}\,e^{\mathrm{SNR}^2/2}(1+\mathrm{SNR}^2)[\operatorname{Erfc}(\mathrm{SNR}/\sqrt2)-2]-2\,\mathrm{SNR}\Big\}.$$
--   3. (Eq. 8.) For every $\kappa\ge0$, $\mathrm{vM}(0,\kappa,\phi)=\mathrm{vM}_0+\mathrm{vM}_2\phi^2+O(\phi^3)$ with $\mathrm{vM}_0=\mathrm{vM}(0,\kappa,0)$ and $\mathrm{vM}_2$ half the second derivative at $0$.
--   4. (Eq. 11.) For every $\kappa\ge0$, $\mathrm{vM}_2/\mathrm{vM}_0=-\kappa/2$.
--   5. (Eqs. 12-13.) For $\kappa\ge0$, the matching condition $P_2/P_0=\mathrm{vM}_2/\mathrm{vM}_0$ holds if and only if $\kappa=\kappa(\mathrm{SNR})$, the expression of eq. (13).
--
--   This is the rule by which the paper assigns a von Mises distribution to a baseline of given signal-to-noise ratio.
--
--   **Formalization Note** The coefficients $P_0,P_2$ are the Taylor coefficients $P(0)$ and $P''(0)/2$. The intermediate eqs. (5), (6) and (10) are not stated: eq. (5) equals $P(0)$ only if the prefactor of eq. (1) is $1/(4\pi)$ rather than the printed $1/(4\pi\sigma)$, eq. (6) has $e^{-V^2/2}$ for $e^{-\mathrm{SNR}^2/2}$, and eq. (10) carries a spurious factor $\phi^2$. The ratio $P_2/P_0$ of eq. (7), and hence eq. (13), does not depend on the prefactor.
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), claim c002; Section 2, eqs. (4), (7), (8), (11), (12), (13), PDF pp. 2-3

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace Arxiv1909_04681

theorem kappa_moment_matching (V σ : ℝ) (hV : 0 < V) (hσ : 0 < σ) :
    ((fun x => truePhaseDensity V σ x -
        (truePhaseDensity V σ 0 + iteratedDeriv 2 (truePhaseDensity V σ) 0 / 2 * x ^ 2))
        =O[𝓝 0] fun x => x ^ 3) ∧
    curvatureRatio (truePhaseDensity V σ) =
      (V / σ) / (2 * (Real.sqrt (2 * Real.pi) * (V / σ) * Real.exp ((V / σ) ^ 2 / 2) *
          (erf ((V / σ) / Real.sqrt 2) + 1) + 2)) *
        (Real.sqrt (2 * Real.pi) * Real.exp ((V / σ) ^ 2 / 2) * (1 + (V / σ) ^ 2) *
          (erfc ((V / σ) / Real.sqrt 2) - 2) - 2 * (V / σ)) ∧
    (∀ κ : ℝ, 0 ≤ κ →
      (fun x => vonMises 0 κ x -
          (vonMises 0 κ 0 + iteratedDeriv 2 (vonMises 0 κ) 0 / 2 * x ^ 2))
          =O[𝓝 0] fun x => x ^ 3) ∧
    (∀ κ : ℝ, 0 ≤ κ → curvatureRatio (vonMises 0 κ) = -κ / 2) ∧
    (∀ κ : ℝ, 0 ≤ κ →
      (curvatureRatio (truePhaseDensity V σ) = curvatureRatio (vonMises 0 κ) ↔
        κ = kappaOfSNR (V / σ))) := by sorry

end Arxiv1909_04681
