-- Prove2me | Theorems.Thm_Feynman1948_free_step_first_order
-- name    : Feynman1948.free_step_first_order
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T17:44:04.527509+00:00
-- url     : https://prove2.me/theorems/76fa396b-8c92-4af3-8ce7-e684e189beb0
-- title:
--   Eq. (27), free particle: first-order term $\frac{\hbar\varepsilon i}{2m}\,\partial_x^2\psi$
-- statement:
--   Let $\hbar,m>0$ and let $\psi$ be a Schwartz function. For the free particle ($V\equiv0$), the one-step evolution $U_\varepsilon$ of Eq. (23) satisfies, at every point $x$,
--   $$\frac{(U_\varepsilon\psi)(x)-\psi(x)}{\varepsilon}\;\longrightarrow\;\frac{\hbar i}{2m}\,\psi''(x)\qquad(\varepsilon\to0^+),$$
--   i.e. the bracket of Eq. (27), $\psi+\frac{\hbar\varepsilon i}{2m}\partial_x^2\psi+\cdots$, is correct to first order in $\varepsilon$.
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, pp. 375-376, Eqs. (25)-(27)

import Mathlib
import Definitions.Def_Feynman1948_WaveEquation

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem free_step_first_order (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m (fun _ => 0) ε ψ x - ψ x) / ε) (𝓝[>] 0)
      (𝓝 (I * ħ / (2 * m) * deriv (deriv ψ) x)) := by sorry

end Feynman1948
