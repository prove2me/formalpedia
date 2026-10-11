-- Prove2me | Theorems.Thm_DarkEnergyLCDM_quintessence_continuity
-- name    : DarkEnergyLCDM.quintessence_continuity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:07:50.564666+00:00
-- url     : https://prove2.me/theorems/b07691c1-2224-4e30-bd4a-f5dc01c49875
-- title:
--   Quintessence as a perfect fluid: $\dot\rho_\phi+3H(\rho_\phi+p_\phi)=0$
-- statement:
--   Let $I$ be an open interval, $a$ any function, $\phi$ a $C^2$ function on $I$ and $V$ a differentiable potential. Suppose the Klein–Gordon equation $\ddot\phi + 3H\dot\phi + V'(\phi) = 0$ (Eq. 15) holds on $I$, with $H = \dot a/a$. Then the density and pressure of Eq. (17), $\rho_\phi = \dot\phi^2/2+V(\phi)$ and $p_\phi = \dot\phi^2/2 - V(\phi)$, satisfy the continuity equation
--   $$\dot\rho_\phi + 3H(\rho_\phi + p_\phi) = 0 \quad\text{on } I.$$
--
--   This makes precise the statement in §3.7 that one can define a fluid that reproduces the same dynamics as the scalar field.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 71–72, Eqs. (15) and (17)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

theorem quintessence_continuity (I : Set ℝ) (hI : IsOpen I) (a ϕ V : ℝ → ℝ)
    (hϕ : ContDiffOn ℝ 2 ϕ I) (hV : Differentiable ℝ V)
    (hKG : ∀ t ∈ I, deriv (deriv ϕ) t + 3 * hubble a t * deriv ϕ t + deriv V (ϕ t) = 0) :
    ∀ t ∈ I, ContinuityEq a (quintessenceDensity V ϕ) (quintessencePressure V ϕ) t := by sorry

end DarkEnergyLCDM
