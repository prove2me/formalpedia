-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_second_law_compression
-- name    : AstrophysicalFluidDynamics.shock_second_law_compression
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:35:45.328464+00:00
-- url     : https://prove2.me/theorems/34036588-9ca2-42e0-85ba-82933765cc5c
-- title:
--   Only compression shocks are physically realizable (Ogilvie 2016, §6.3.2)
-- statement:
--   For a normal non-magnetic shock in a perfect gas with $\gamma>1$, with positive upstream and downstream states satisfying the Rankine–Hugoniot relations and differing from each other, suppose the entropy does not decrease across the shock, $[s]_1^2 \ge 0$ (second law of thermodynamics). Then the shock is a compression shock:
--   $$M_1 > 1,\qquad M_2 < 1,\qquad \rho_2 > \rho_1,\qquad p_2 > p_1.$$
--
--   In words: the shock travels supersonically relative to the upstream gas and subsonically relative to the downstream gas, and it compresses the gas; rarefaction shocks are excluded.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, p. 39; Example A.13, p. 90

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_second_law_compression
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁))
    (hentropy : 0 ≤ entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂) :
    1 < machNumber γ ρ₁ u₁ p₁ ∧ machNumber γ ρ₂ u₂ p₂ < 1 ∧ ρ₁ < ρ₂ ∧ p₁ < p₂ := by sorry

end AstrophysicalFluidDynamics
