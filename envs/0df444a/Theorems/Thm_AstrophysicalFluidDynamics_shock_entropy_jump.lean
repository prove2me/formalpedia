-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_entropy_jump
-- name    : AstrophysicalFluidDynamics.shock_entropy_jump
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T18:52:19.51798+00:00
-- url     : https://prove2.me/theorems/bb2e69f3-d5d9-4420-93ea-866b364bc43e
-- title:
--   Entropy change across a shock (Ogilvie 2016, Example A.13, eq. A 28)
-- statement:
--   For a perfect gas with $\gamma > 1$, let positive upstream and downstream states $(\rho_1,u_1,p_1)$, $(\rho_2,u_2,p_2)$ satisfy the Rankine–Hugoniot relations. Writing $P = p_2/p_1$ for the pressure ratio, the entropy change across the shock is
--   $$\frac{[s]_1^2}{c_v} = \ln P - \gamma\ln\left[\frac{(\gamma+1)P + (\gamma-1)}{(\gamma-1)P + (\gamma+1)}\right],$$
--   where the specific entropy of a perfect gas is $s = c_p(\gamma^{-1}\ln p - \ln\rho) + \text{const}$, so that $[s]_1^2/c_v = \ln(p_2/p_1) - \gamma\ln(\rho_2/\rho_1)$.
--
--   This formula is the basis for the second-law argument that excludes rarefaction shocks.
--
--   **Formalization Note** The formula also holds, trivially, when the two states coincide, so the non-degeneracy hypothesis is not included here.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, Example A.13, eq. (A 28), p. 90; entropy of a perfect gas §11.6.2

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_entropy_jump
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂) :
    entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂ =
      Real.log (p₂ / p₁) -
        γ * Real.log (((γ + 1) * (p₂ / p₁) + (γ - 1)) / ((γ - 1) * (p₂ / p₁) + (γ + 1))) := by sorry

end AstrophysicalFluidDynamics
