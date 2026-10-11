-- Prove2me | Theorems.Thm_DarkEnergyLCDM_radiation_density_scaling
-- name    : DarkEnergyLCDM.radiation_density_scaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:00:06.807977+00:00
-- url     : https://prove2.me/theorems/0fff8c4f-c90b-47a7-b0b5-a878bf36f350
-- title:
--   Radiation density scales as $a^{-4}$
-- statement:
--   Let $I$ be an open connected interval, and let $a$ and $\rho$ be differentiable on $I$ with $a>0$ there. Suppose $\rho$ satisfies the continuity equation with the radiation equation of state $p=\rho/3$:
--   $$\dot\rho + 3H\left(\rho + \tfrac{\rho}{3}\right) = 0 \quad\text{on } I.$$
--   If $t_0\in I$ and $a(t_0)=1$, then $\rho(t) = \rho(t_0)\,a(t)^{-4}$ for all $t\in I$.
--
--   This is the first half of Eq. (4): radiation dilutes as $a^{-4}$.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, Eq. (4) (radiation, $w_r = 1/3$)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

theorem radiation_density_scaling (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (a ρ : ℝ → ℝ) (ha : DifferentiableOn ℝ a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hρ : DifferentiableOn ℝ ρ I)
    (hcont : ∀ t ∈ I, ContinuityEq a ρ (fun s => ρ s / 3) t)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1) :
    ∀ t ∈ I, ρ t = ρ t₀ * (a t)⁻¹ ^ 4 := by sorry

end DarkEnergyLCDM
