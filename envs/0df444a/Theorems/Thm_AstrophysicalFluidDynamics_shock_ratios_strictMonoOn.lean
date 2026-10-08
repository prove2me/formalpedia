-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_ratios_strictMonoOn
-- name    : AstrophysicalFluidDynamics.shock_ratios_strictMonoOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T17:34:26.084136+00:00
-- url     : https://prove2.me/theorems/5fe35570-a06e-451f-ba5a-e1ba37aadac8
-- title:
--   The shock density and pressure ratios increase with $M_1$ (Ogilvie 2016, §6.3.2)
-- statement:
--   Let $\gamma > 1$. The functions
--   $$D(M_1) = \frac{(\gamma+1)M_1^2}{(\gamma-1)M_1^2+2},\qquad P(M_1) = \frac{2\gamma M_1^2-(\gamma-1)}{\gamma+1}$$
--   giving the density and pressure ratios across a shock are strictly increasing functions of the upstream Mach number on $M_1 > 0$.
--
--   This is the remark following (6.31) in the source; it underlies the classification of shocks into compression and rarefaction shocks.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, p. 39 (remark after eq. (6.31))

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_ratios_strictMonoOn
    (γ : ℝ) (hγ : 1 < γ) :
    StrictMonoOn (shockDensityRatio γ) (Set.Ioi 0) ∧
    StrictMonoOn (shockPressureRatio γ) (Set.Ioi 0) := by sorry

end AstrophysicalFluidDynamics
