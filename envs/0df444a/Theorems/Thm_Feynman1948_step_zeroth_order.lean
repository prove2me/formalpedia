-- Prove2me | Theorems.Thm_Feynman1948_step_zeroth_order
-- name    : Feynman1948.step_zeroth_order
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T17:32:50.239892+00:00
-- url     : https://prove2.me/theorems/f3af6ac0-fef1-498a-9089-25d314eaa274
-- title:
--   Eqs. (27)–(28): with $A=(2\pi\hbar\varepsilon i/m)^{1/2}$ both sides agree to zero order in $\varepsilon$
-- statement:
--   Let $\hbar,m>0$, let $V:\mathbb R\to\mathbb R$ be any potential and let $\psi$ be a Schwartz function (smooth and rapidly decreasing, the paper's "relatively smooth" wave function that "falls off sufficiently for large $x$"). With the normalization $A=(2\pi\hbar\varepsilon i/m)^{1/2}$ of Eq. (28), the one-step evolution of Eq. (23) agrees with $\psi$ to zero order in $\varepsilon$: for every $x$,
--   $$\frac{1}{A}\int \exp\!\Big[\frac{i\varepsilon}{\hbar}\Big\{\frac m2\Big(\frac{x-y}{\varepsilon}\Big)^2 - V(x)\Big\}\Big]\psi(y)\,dy \;\longrightarrow\; \psi(x)\qquad(\varepsilon\to0^+).$$
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, pp. 375-376, Eqs. (23)-(28)

import Mathlib
import Definitions.Def_Feynman1948_WaveEquation

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem step_zeroth_order (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (V : ℝ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => stepEvolution ħ m V ε ψ x) (𝓝[>] 0) (𝓝 (ψ x)) := by sorry

end Feynman1948
