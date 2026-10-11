-- Prove2me | Theorems.Thm_DarkEnergyLCDM_matter_density_scaling
-- name    : DarkEnergyLCDM.matter_density_scaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:02:24.007201+00:00
-- url     : https://prove2.me/theorems/59d83cb0-0c19-4a96-a023-c94b842228a8
-- title:
--   Matter density scales as $a^{-3}$
-- statement:
--   Let $I$ be an open connected interval, and let $a$ and $\rho$ be differentiable on $I$ with $a>0$ there. Suppose $\rho$ satisfies the continuity equation for pressureless matter ($p = 0$):
--   $$\dot\rho + 3H\rho = 0 \quad\text{on } I.$$
--   If $t_0\in I$ and $a(t_0)=1$, then $\rho(t) = \rho(t_0)\,a(t)^{-3}$ for all $t\in I$.
--
--   This is the second half of Eq. (4): pressureless matter dilutes with the volume, as $a^{-3}$.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, Eq. (4) (matter, $w_m = 0$)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

theorem matter_density_scaling (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (a ρ : ℝ → ℝ) (ha : DifferentiableOn ℝ a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hρ : DifferentiableOn ℝ ρ I)
    (hcont : ∀ t ∈ I, ContinuityEq a ρ (fun _ => 0) t)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1) :
    ∀ t ∈ I, ρ t = ρ t₀ * (a t)⁻¹ ^ 3 := by sorry

end DarkEnergyLCDM
