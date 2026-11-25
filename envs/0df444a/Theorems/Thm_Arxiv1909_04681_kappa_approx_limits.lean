-- Prove2me | Theorems.Thm_Arxiv1909_04681_kappa_approx_limits
-- name    : Arxiv1909_04681.kappa_approx_limits
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:48:55.894226+00:00
-- url     : https://prove2.me/theorems/f3ecede0-fbf5-5a90-a07b-a8f20e0ecd0f
-- title:
--   Eq. (14): the approximation of $\kappa(\mathrm{SNR})$ matches both limits of eq. (13)
-- statement:
--   Let $\kappa(\mathrm{SNR})$ be the moment-matched concentration parameter of eq. (13) and $\kappa_{\approx}(\mathrm{SNR})=\dfrac{\sqrt{\pi/2}\,\mathrm{SNR}}{1+\sqrt{\pi/2}\,\mathrm{SNR}}+\mathrm{SNR}^2$ its approximation, eq. (14). Both have the same behaviour in both limits:
--
--   1. As $\mathrm{SNR}\to0^+$, $$\kappa(\mathrm{SNR})\sim\sqrt{\pi/2}\,\mathrm{SNR}\quad\text{and}\quad\kappa_{\approx}(\mathrm{SNR})\sim\sqrt{\pi/2}\,\mathrm{SNR}$$ (the ratios tend to $1$).
--   2. As $\mathrm{SNR}\to\infty$, $$\kappa(\mathrm{SNR})-(1+\mathrm{SNR}^2)\to0\quad\text{and}\quad\kappa_{\approx}(\mathrm{SNR})-(1+\mathrm{SNR}^2)\to0.$$
--
--   This is the content of the paper's statement that eq. (14) is obtained by asymptotically matching the limits of eq. (13).
--
--   **Formalization Note** The paper does not write the limits out. They are read off from the form of eq. (14): $\sqrt{\pi/2}\,\mathrm{SNR}$ at small SNR, and $1+\mathrm{SNR}^2$, including the constant $1$, at large SNR, which is why the large-SNR limit is stated for the difference rather than the ratio.
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), claim c003; Section 2, eqs. (13)-(14), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace Arxiv1909_04681

theorem kappa_approx_limits :
    IsEquivalent (𝓝[>] 0) kappaOfSNR (fun S => Real.sqrt (Real.pi / 2) * S) ∧
    IsEquivalent (𝓝[>] 0) kappaApprox (fun S => Real.sqrt (Real.pi / 2) * S) ∧
    Tendsto (fun S => kappaOfSNR S - (1 + S ^ 2)) atTop (𝓝 0) ∧
    Tendsto (fun S => kappaApprox S - (1 + S ^ 2)) atTop (𝓝 0) := by sorry

end Arxiv1909_04681
