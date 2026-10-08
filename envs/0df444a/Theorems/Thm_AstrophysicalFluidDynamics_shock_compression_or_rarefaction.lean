-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_shock_compression_or_rarefaction
-- name    : AstrophysicalFluidDynamics.shock_compression_or_rarefaction
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T18:07:10.527775+00:00
-- url     : https://prove2.me/theorems/ae7ab585-182e-4b1c-8cde-ccb743e03e2a
-- title:
--   Compression vs. rarefaction shocks (Ogilvie 2016, §6.3.2)
-- statement:
--   For a normal non-magnetic shock in a perfect gas with $\gamma>1$, with positive upstream and downstream states satisfying the Rankine–Hugoniot relations and differing from each other, let $M_1$, $M_2$ be the upstream and downstream Mach numbers. Then:
--
--   1. $M_1 \neq 1$ (the case $M_1 = 1$ corresponds only to the trivial, continuous solution);
--   2. if $M_1 > 1$, then $M_2 < 1$, $\rho_2 > \rho_1$ and $p_2 > p_1$ (a **compression shock**);
--   3. if $M_1 < 1$, then $M_2 > 1$, $\rho_2 < \rho_1$ and $p_2 < p_1$ (a **rarefaction shock**).
--
--   This is the classification of the non-trivial solutions of the Rankine–Hugoniot relations given after (6.31).
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, p. 39 (paragraph after eq. (6.31))

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem shock_compression_or_rarefaction
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    machNumber γ ρ₁ u₁ p₁ ≠ 1 ∧
    (1 < machNumber γ ρ₁ u₁ p₁ → machNumber γ ρ₂ u₂ p₂ < 1 ∧ ρ₁ < ρ₂ ∧ p₁ < p₂) ∧
    (machNumber γ ρ₁ u₁ p₁ < 1 → 1 < machNumber γ ρ₂ u₂ p₂ ∧ ρ₂ < ρ₁ ∧ p₂ < p₁) := by sorry

end AstrophysicalFluidDynamics
