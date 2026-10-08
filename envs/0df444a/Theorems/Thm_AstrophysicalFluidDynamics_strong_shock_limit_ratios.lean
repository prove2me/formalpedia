-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_strong_shock_limit_ratios
-- name    : AstrophysicalFluidDynamics.strong_shock_limit_ratios
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T22:00:11.846989+00:00
-- url     : https://prove2.me/theorems/eada03de-f46f-45f2-a342-255ad7409dd5
-- title:
--   Strong-shock limits of the jump ratios (Ogilvie 2016, eqs. 6.32a–c)
-- statement:
--   Let $\gamma > 1$. In the strong-shock limit $M_1 \to \infty$,
--   $$\frac{(\gamma+1)M_1^2}{(\gamma-1)M_1^2+2} \to \frac{\gamma+1}{\gamma-1},\qquad \frac{2\gamma M_1^2-(\gamma-1)}{\gamma+1} \to \infty,\qquad \frac{2+(\gamma-1)M_1^2}{2\gamma M_1^2-(\gamma-1)} \to \frac{\gamma-1}{2\gamma}.$$
--   That is, the compression ratio $\rho_2/\rho_1$ stays finite (equal to $4$ when $\gamma = 5/3$), the pressure ratio grows without bound, and $M_2^2$ tends to $(\gamma-1)/(2\gamma)$.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, eqs. (6.32a–c), p. 39

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem strong_shock_limit_ratios
    (γ : ℝ) (hγ : 1 < γ) :
    Tendsto (shockDensityRatio γ) atTop (𝓝 ((γ + 1) / (γ - 1))) ∧
    Tendsto (shockPressureRatio γ) atTop atTop ∧
    Tendsto (shockDownstreamMachSq γ) atTop (𝓝 ((γ - 1) / (2 * γ))) := by sorry

end AstrophysicalFluidDynamics
