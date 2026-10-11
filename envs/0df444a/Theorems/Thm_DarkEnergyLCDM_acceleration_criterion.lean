-- Prove2me | Theorems.Thm_DarkEnergyLCDM_acceleration_criterion
-- name    : DarkEnergyLCDM.acceleration_criterion
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:03:57.053345+00:00
-- url     : https://prove2.me/theorems/fff2627f-12e5-4aa4-b616-056c6cdfc23d
-- title:
--   Acceleration criterion $\ddot a>0 \iff \Lambda > 4\pi G(\rho+3p)$
-- statement:
--   Let $a,\rho,p$ be real functions of time and $G,\Lambda$ real constants. Let $t$ be an instant with $a(t)>0$ at which the acceleration equation (7) holds. Then
--   $$\ddot a(t) > 0 \iff \Lambda > 4\pi G\,(\rho(t) + 3p(t)).$$
--
--   This is Eq. (8), the condition the cosmological constant must satisfy for the expansion to accelerate.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, Eq. (8)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Real

theorem acceleration_criterion (G Λ : ℝ) (a ρ p : ℝ → ℝ) (t : ℝ) (ha : 0 < a t)
    (hacc : AccelerationEq G Λ a ρ p t) :
    0 < deriv (deriv a) t ↔ 4 * π * G * (ρ t + 3 * p t) < Λ := by sorry

end DarkEnergyLCDM
