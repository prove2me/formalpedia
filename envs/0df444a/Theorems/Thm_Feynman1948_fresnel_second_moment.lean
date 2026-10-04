-- Prove2me | Theorems.Thm_Feynman1948_fresnel_second_moment
-- name    : Feynman1948.fresnel_second_moment
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T17:08:43.685091+00:00
-- url     : https://prove2.me/theorems/d5a776e9-fcde-4c95-a13e-9d19d4b33ff7
-- title:
--   Eq. (26), third integral: $\int e^{im\xi^2/2\hbar\varepsilon}\,\xi^2\,d\xi = (\hbar\varepsilon i/m)(2\pi\hbar\varepsilon i/m)^{1/2}$
-- statement:
--   Let $\hbar, m, \varepsilon > 0$. The third integral of Eq. (26),
--   $$\int_{-\infty}^{\infty}\exp(im\xi^2/2\hbar\varepsilon)\,\xi^2\,d\xi = \frac{\hbar\varepsilon i}{m}\Big(\frac{2\pi\hbar\varepsilon i}{m}\Big)^{1/2},$$
--   understood with the convergence factor of footnote 13: $M_2(\delta)=\int_{\mathbb R}\xi^2\exp\big(im\xi^2/(2\hbar(1-i\delta)\varepsilon)\big)\,d\xi \to (\hbar\varepsilon i/m)\,A$ as $\delta\to0^+$.
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, p. 375, Eq. (26), third formula; footnote 13 (p. 376)

import Mathlib
import Definitions.Def_Feynman1948_WaveEquation

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem fresnel_second_moment (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => regularizedMoment ħ m ε δ 2) (𝓝[>] 0)
      (𝓝 (ħ * ε * I / m * normalizingFactor ħ m ε)) := by sorry

end Feynman1948
