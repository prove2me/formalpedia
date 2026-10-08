-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_rankine_hugoniot_shock_relations
-- name    : AstrophysicalFluidDynamics.rankine_hugoniot_shock_relations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T15:48:33.214976+00:00
-- url     : https://prove2.me/theorems/19441381-b62b-437e-9699-f275b7fef998
-- title:
--   Rankine–Hugoniot shock relations for a perfect gas (Ogilvie 2016, eqs. 6.30–6.31)
-- statement:
--   Consider a normal, non-magnetic shock at rest in a perfect gas with adiabatic exponent $\gamma > 1$. Let the upstream state be $(\rho_1, u_1, p_1)$ and the downstream state $(\rho_2, u_2, p_2)$, with all densities, normal velocities and pressures positive, related by the Rankine–Hugoniot relations
--   $$[\rho u]_1^2 = 0,\qquad [\rho u^2 + p]_1^2 = 0,\qquad \Big[\rho u\big(\tfrac12u^2 + \tfrac{\gamma}{\gamma-1}\tfrac{p}{\rho}\big)\Big]_1^2 = 0,$$
--   and suppose the two states are different (a genuine discontinuity). Let $M_1 = u_1/v_{s1}$ and $M_2 = u_2/v_{s2}$ be the upstream and downstream Mach numbers, where $v_s = (\gamma p/\rho)^{1/2}$. Then
--   $$\frac{\rho_2}{\rho_1} = \frac{u_1}{u_2} = \frac{(\gamma+1)M_1^2}{(\gamma-1)M_1^2+2},\qquad \frac{p_2}{p_1} = \frac{2\gamma M_1^2-(\gamma-1)}{\gamma+1},\qquad M_2^2 = \frac{2+(\gamma-1)M_1^2}{2\gamma M_1^2-(\gamma-1)}.$$
--
--   These are the jump conditions that determine the post-shock state of a gas from the pre-shock state and the shock Mach number; they are used throughout astrophysics, for example in the supernova blast-wave problem.
--
--   **Formalization Note** The hypothesis that the two states differ excludes the trivial solution (identical states), for which the Rankine–Hugoniot relations hold for every Mach number.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, eqs. (6.27)–(6.31), pp. 38–39; Example A.13, eqs. (A 22)–(A 27), pp. 89–90

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem rankine_hugoniot_shock_relations
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    ρ₂ / ρ₁ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    u₁ / u₂ = shockDensityRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    p₂ / p₁ = shockPressureRatio γ (machNumber γ ρ₁ u₁ p₁) ∧
    (machNumber γ ρ₂ u₂ p₂) ^ 2 = shockDownstreamMachSq γ (machNumber γ ρ₁ u₁ p₁) := by sorry

end AstrophysicalFluidDynamics
