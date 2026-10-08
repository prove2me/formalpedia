-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_downstream_mach_sq
-- name    : AstrophysicalFluidDynamics.shock_downstream_mach_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T17:17:28.991786+00:00
-- url     : https://prove2.me/theorems/d7b6ec90-05cc-4e38-813e-39eb2d8d88b9
-- title:
--   Downstream Mach number of a shock (Ogilvie 2016, eq. 6.31)
-- statement:
--   Under the same hypotheses, the downstream Mach number $M_2 = u_2/(\gamma p_2/\rho_2)^{1/2}$ satisfies
--   $$M_2^2 = \frac{2+(\gamma-1)M_1^2}{2\gamma M_1^2-(\gamma-1)},$$
--   where $M_1 = u_1/(\gamma p_1/\rho_1)^{1/2}$ is the upstream Mach number.
--
--   This relation shows that the flow is supersonic on one side of the shock and subsonic on the other.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, eq. (6.31), p. 39; Example A.13, eq. (A 27)

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_downstream_mach_sq
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    (machNumber γ ρ₂ u₂ p₂) ^ 2 = shockDownstreamMachSq γ (machNumber γ ρ₁ u₁ p₁) := by sorry

end AstrophysicalFluidDynamics
