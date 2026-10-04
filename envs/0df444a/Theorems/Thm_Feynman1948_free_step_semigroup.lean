-- Prove2me | Theorems.Thm_Feynman1948_free_step_semigroup
-- name    : Feynman1948.free_step_semigroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T17:51:14.202698+00:00
-- url     : https://prove2.me/theorems/cdd3ff07-daaa-4954-8a6e-10d6a10d4660
-- title:
--   Footnote 15: Eq. (18) is exact for the free particle ($U_\varepsilon U_\delta = U_{\varepsilon+\delta}$)
-- statement:
--   Footnote 15 states that Eq. (18) is exact, for arbitrary $\varepsilon$, when the exact classical action (11) is used and the potential is at most quadratic, e.g. for the free particle. For the free particle the exact action (11) over a time $\varepsilon$ is $\frac{m\varepsilon}{2}\big(\frac{x_{k+1}-x_k}{\varepsilon}\big)^2$ (Eq. 22 with $V=0$), and exactness means that the one-step evolutions compose: for $\hbar,m>0$, $\varepsilon,\delta>0$ and a Schwartz function $\psi$,
--   $$U_\varepsilon\big(U_\delta\psi\big)(x) = \big(U_{\varepsilon+\delta}\psi\big)(x)\quad\text{for all }x.$$
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, p. 376, footnote 15; Eqs. (11), (18), (22)

import Mathlib
import Definitions.Def_Feynman1948_WaveEquation

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem free_step_semigroup (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m)
    (ψ : 𝓢(ℝ, ℂ)) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (x : ℝ) :
    stepEvolution ħ m (fun _ => 0) ε (stepEvolution ħ m (fun _ => 0) δ ψ) x =
      stepEvolution ħ m (fun _ => 0) (ε + δ) ψ x := by sorry

end Feynman1948
