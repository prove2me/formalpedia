-- Prove2me | Theorems.Thm_DarkEnergyLCDM_vacuum_energy_as_lambda
-- name    : DarkEnergyLCDM.vacuum_energy_as_lambda
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:05:06.744355+00:00
-- url     : https://prove2.me/theorems/f7ba0f79-a5eb-48f6-a92c-fcfe2b0fa936
-- title:
--   Vacuum energy $\rho=\Lambda/(8\pi G)$, $p=-\rho$ is equivalent to $\Lambda$
-- statement:
--   Let $G\neq0$, let $K,\Lambda$ be constants, and set $\rho_\Lambda = \Lambda/(8\pi G)$. For any functions $a,\rho,p$ and any instant $t$:
--
--   1. The Friedmann equation with constant $\Lambda$ and density $\rho$ holds at $t$ if and only if the Friedmann equation with $\Lambda = 0$ and density $\rho + \rho_\Lambda$ holds at $t$.
--   2. The acceleration equation with $\Lambda$ and $(\rho, p)$ holds at $t$ if and only if the acceleration equation with $\Lambda=0$ and $(\rho+\rho_\Lambda,\ p-\rho_\Lambda)$ holds at $t$.
--   3. The constant density $\rho_\Lambda$ with pressure $-\rho_\Lambda$ (so $w_\Lambda=-1$) satisfies the continuity equation at $t$.
--
--   This makes precise the remark after Eq. (9): the vacuum stress tensor $T^{(\rm vac)}_{\mu\nu} = -\frac{\Lambda^{(\rm vac)}}{8\pi G}g_{\mu\nu}$ coincides with the cosmological-constant term. It also matches the description in §3.7 of $\Lambda$ as a fluid with constant energy density and $w_\Lambda=-1$.
--
--   **Formalization Note** The equivalence is stated at the level of the background equations (2), (3) and (7), not of the full Einstein tensor equation.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, Eq. (9) and following text; p. 71, §3.7

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Real

theorem vacuum_energy_as_lambda (G K Λ : ℝ) (hG : G ≠ 0) (a ρ p : ℝ → ℝ) (t : ℝ) :
    (FriedmannEq G K Λ a ρ t ↔
      FriedmannEq G K 0 a (fun s => ρ s + Λ / (8 * π * G)) t) ∧
    (AccelerationEq G Λ a ρ p t ↔
      AccelerationEq G 0 a (fun s => ρ s + Λ / (8 * π * G))
        (fun s => p s - Λ / (8 * π * G)) t) ∧
    ContinuityEq a (fun _ => Λ / (8 * π * G)) (fun _ => -(Λ / (8 * π * G))) t := by sorry

end DarkEnergyLCDM
