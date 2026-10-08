-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_entropy_sign
-- name    : AstrophysicalFluidDynamics.shock_entropy_sign
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T21:19:01.037999+00:00
-- url     : https://prove2.me/theorems/fc375218-acb7-40bf-a840-e766a4ccc31a
-- title:
--   Sign of the entropy change across a shock (Ogilvie 2016, §6.3.2 / Example A.13)
-- statement:
--   For a normal non-magnetic shock in a perfect gas with $\gamma>1$, with positive upstream and downstream states satisfying the Rankine–Hugoniot relations and differing from each other, the entropy change $[s]_1^2/c_v = \ln(p_2/p_1) - \gamma\ln(\rho_2/\rho_1)$ is
--
--   1. strictly positive for a compression shock ($M_1 > 1$), and
--   2. strictly negative for a rarefaction shock ($M_1 < 1$).
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, p. 39; Example A.13, p. 90

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_entropy_sign
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    (1 < machNumber γ ρ₁ u₁ p₁ → 0 < entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂) ∧
    (machNumber γ ρ₁ u₁ p₁ < 1 → entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂ < 0) := by sorry

end AstrophysicalFluidDynamics
