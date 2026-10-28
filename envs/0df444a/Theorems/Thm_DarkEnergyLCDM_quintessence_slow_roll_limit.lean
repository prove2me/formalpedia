-- Prove2me | Theorems.Thm_DarkEnergyLCDM_quintessence_slow_roll_limit
-- name    : DarkEnergyLCDM.quintessence_slow_roll_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:08:47.670534+00:00
-- url     : https://prove2.me/theorems/cfacc7f6-472e-475b-adf8-e69f6b45150a
-- title:
--   Slow roll: $w_\phi\to-1$ as $\dot\phi\to0$
-- statement:
--   Let $V\neq0$ be a fixed value of the potential, and let
--   $$w_\phi(\dot\phi, V) = \frac{\dot\phi^2/2 - V}{\dot\phi^2/2 + V}$$
--   be the quintessence equation of state $p_\phi/\rho_\phi$. Then $w_\phi(\dot\phi, V) \to -1$ as $\dot\phi\to0$.
--
--   This is the slow-roll statement after Eq. (18): when $\dot\phi^2\to0$, $w_\phi\to-1$.
--
--   **Formalization Note** The printed Eq. (18) reads $w_\phi = (\dot\phi^2+2V)/(\dot\phi^2-2V)$, which is the reciprocal of $p_\phi/\rho_\phi$ computed from Eq. (17). The ratio $p_\phi/\rho_\phi$ is used here. Both expressions tend to $-1$.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 72, Eqs. (17)–(18) and following sentence

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Filter Topology

theorem quintessence_slow_roll_limit (V : ℝ) (hV : V ≠ 0) :
    Tendsto (fun ϕdot : ℝ => quintessenceEOS ϕdot V) (𝓝 0) (𝓝 (-1)) := by sorry

end DarkEnergyLCDM
