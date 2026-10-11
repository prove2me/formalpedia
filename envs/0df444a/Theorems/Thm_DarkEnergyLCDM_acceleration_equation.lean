-- Prove2me | Theorems.Thm_DarkEnergyLCDM_acceleration_equation
-- name    : DarkEnergyLCDM.acceleration_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:03:27.900111+00:00
-- url     : https://prove2.me/theorems/cb243b56-b911-407d-81f1-db977fdd3f1a
-- title:
--   Acceleration equation $\ddot a/a = -\frac{4\pi G}{3}(\rho+3p)+\frac{\Lambda}{3}$
-- statement:
--   Let $(a, \rho_r, \rho_m)$ be a ΛCDM background on $I$ with constants $G, K, \Lambda$, and let $t\in I$ with $\dot a(t)\neq 0$. Then at $t$
--   $$\frac{\ddot a}{a} = -\frac{4\pi G}{3}(\rho + 3p) + \frac{\Lambda}{3},\qquad \rho = \rho_r + \rho_m,\quad p = \rho_r/3.$$
--
--   This is Eq. (7), the second-order equation for the scale factor.
--
--   **Formalization Note** The source obtains Eq. (7) from the Einstein field equations. Here it is derived from the Friedmann and continuity equations, which determine it wherever $\dot a\neq 0$. At instants with $\dot a = 0$ it is not a consequence of them, so those instants are excluded.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, Eq. (7)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

theorem acceleration_equation (G K Λ : ℝ) (I : Set ℝ) (a ρr ρm : ℝ → ℝ)
    (hbg : IsLCDMBackground G K Λ I a ρr ρm) (t : ℝ) (ht : t ∈ I) (hda : deriv a t ≠ 0) :
    AccelerationEq G Λ a (fun s => ρr s + ρm s) (fun s => ρr s / 3) t := by sorry

end DarkEnergyLCDM
