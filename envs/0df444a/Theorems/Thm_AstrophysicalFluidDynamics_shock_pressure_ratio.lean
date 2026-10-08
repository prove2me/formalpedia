-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_pressure_ratio
-- name    : AstrophysicalFluidDynamics.shock_pressure_ratio
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T16:46:48.625041+00:00
-- url     : https://prove2.me/theorems/0ec3f999-db59-4f79-b88b-b9ef4ad321d6
-- title:
--   Shock pressure ratio $p_2/p_1$ (Ogilvie 2016, eq. 6.30b)
-- statement:
--   Under the same hypotheses (perfect gas with $\gamma>1$, positive upstream and downstream states satisfying the Rankine–Hugoniot relations and differing from each other), the pressure ratio across the shock is
--   $$\frac{p_2}{p_1} = \frac{2\gamma M_1^2-(\gamma-1)}{\gamma+1},$$
--   where $M_1 = u_1/(\gamma p_1/\rho_1)^{1/2}$ is the upstream Mach number.
--
--   Together with the density ratio this determines the downstream thermodynamic state.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, eq. (6.30b), p. 38; Example A.13, eq. (A 26b)

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_pressure_ratio
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    p₂ / p₁ = shockPressureRatio γ (machNumber γ ρ₁ u₁ p₁) := by sorry

end AstrophysicalFluidDynamics
