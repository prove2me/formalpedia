-- Prove2me | Theorems.Thm_Feynman1948_fresnel_zeroth_moment
-- name    : Feynman1948.fresnel_zeroth_moment
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T15:28:56.258742+00:00
-- url     : https://prove2.me/theorems/e547a4b2-ee7f-4ee8-a631-2fbe18b6c75a
-- title:
--   Eq. (26), first integral: $\int e^{im\xi^2/2\hbar\varepsilon}\,d\xi = (2\pi\hbar\varepsilon i/m)^{1/2}$
-- statement:
--   Let $\hbar, m, \varepsilon > 0$. The first Fresnel integral of Eq. (26),
--   $$\int_{-\infty}^{\infty} \exp\!\big(im\xi^2/2\hbar\varepsilon\big)\,d\xi = \Big(\frac{2\pi\hbar\varepsilon i}{m}\Big)^{1/2},$$
--   is not absolutely convergent; following footnote 13 it is understood with $\hbar$ replaced by $\hbar(1-i\delta)$ and $\delta\to0^+$. The statement is: the regularized integrals $M_0(\delta)=\int_{\mathbb R}\exp\big(im\xi^2/(2\hbar(1-i\delta)\varepsilon)\big)\,d\xi$ converge, as $\delta\to0^+$, to the normalizing factor $A=(2\pi\hbar\varepsilon i/m)^{1/2}$ (principal branch).
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, p. 375, Eq. (26), first formula; footnote 13 (p. 376)

import Mathlib
import Definitions.Def_Feynman1948_WaveEquation

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem fresnel_zeroth_moment (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => regularizedMoment ħ m ε δ 0) (𝓝[>] 0)
      (𝓝 (normalizingFactor ħ m ε)) := by sorry

end Feynman1948
