-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_density_ratio
-- name    : AstrophysicalFluidDynamics.shock_density_ratio
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T16:11:58.94599+00:00
-- url     : https://prove2.me/theorems/d8b9afbe-1c3f-4fd4-bafd-53924b329dc5
-- title:
--   Shock compression ratio $\rho_2/\rho_1 = u_1/u_2$ (Ogilvie 2016, eq. 6.30a)
-- statement:
--   For a normal non-magnetic shock in a perfect gas with $\gamma>1$, with positive upstream state $(\rho_1,u_1,p_1)$ and positive downstream state $(\rho_2,u_2,p_2)$ satisfying the Rankine–Hugoniot relations (6.27) and differing from each other, the density (compression) ratio and the inverse velocity ratio are both given by the upstream Mach number $M_1 = u_1/(\gamma p_1/\rho_1)^{1/2}$:
--   $$\frac{\rho_2}{\rho_1} = \frac{u_1}{u_2} = \frac{(\gamma+1)M_1^2}{(\gamma-1)M_1^2+2}.$$
--
--   This is the first of the Rankine–Hugoniot jump formulas; the equality $\rho_2/\rho_1 = u_1/u_2$ expresses continuity of the mass flux.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, eq. (6.30a), p. 38; Example A.13, eq. (A 26a)

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_density_ratio
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    ρ₂ / ρ₁ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    u₁ / u₂ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) := by sorry

end AstrophysicalFluidDynamics
