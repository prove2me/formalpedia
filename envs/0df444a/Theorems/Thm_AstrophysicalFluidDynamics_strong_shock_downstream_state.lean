-- Prove2me | Theorems.Thm_AstrophysicalFluidDynamics_strong_shock_downstream_state
-- name    : AstrophysicalFluidDynamics.strong_shock_downstream_state
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T22:25:42.770004+00:00
-- url     : https://prove2.me/theorems/fc6c88b3-7327-4841-8f26-740905c4fc96
-- title:
--   Downstream state behind a strong shock (Ogilvie 2016, eqs. 6.33–6.34)
-- statement:
--   Let $\gamma > 1$ and fix the upstream density $\rho_1 > 0$ and upstream normal velocity $u_1 > 0$ in the shock frame; in the rest frame of the undisturbed upstream gas the shock speed is $u_{sh} = -u_1$. In the strong-shock limit, obtained by letting the upstream pressure $p_1 \to 0^+$ (so that $M_1 \to \infty$), every positive downstream state $(\rho_2,u_2,p_2)$ that satisfies the Rankine–Hugoniot relations with $(\rho_1,u_1,p_1)$ and differs from it satisfies
--   $$\rho_2 \to \frac{\gamma+1}{\gamma-1}\rho_1,\qquad u_2 - u_1 \to \frac{2u_{sh}}{\gamma+1},\qquad p_2 \to \frac{2\rho_1u_{sh}^2}{\gamma+1},\qquad e_2 = \frac{p_2}{(\gamma-1)\rho_2} \to \frac{2u_{sh}^2}{(\gamma+1)^2}.$$
--   Precisely: for every $\varepsilon>0$ there is $\delta>0$ such that whenever $0<p_1<\delta$, each of the four quantities is within $\varepsilon$ of its limit.
--
--   This is the downstream state used as the boundary condition of the Sedov–Taylor blast-wave solution (§7), and (6.34) records that a strong shock converts a large amount of kinetic energy into thermal energy.
--
--   **Formalization Note** The source's strong-shock limit $M_1 \gg 1$ at fixed $\rho_1$ and shock speed is expressed as $p_1 \to 0^+$; the shock speed $u_{sh}$ is written out as $-u_1$.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §6.3.2, eqs. (6.33a–c), (6.34), p. 39

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics

theorem strong_shock_downstream_state
    (γ ρ₁ u₁ : ℝ) (hγ : 1 < γ) (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) :
    ∀ ε > 0, ∃ δ > 0, ∀ p₁ ρ₂ u₂ p₂ : ℝ, 0 < p₁ → p₁ < δ →
      0 < ρ₂ → 0 < u₂ → 0 < p₂ →
      RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ → (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁) →
        |ρ₂ - (γ + 1) / (γ - 1) * ρ₁| < ε ∧
        |(u₂ - u₁) - 2 * (-u₁) / (γ + 1)| < ε ∧
        |p₂ - 2 * ρ₁ * (-u₁) ^ 2 / (γ + 1)| < ε ∧
        |perfectGasInternalEnergy γ p₂ ρ₂ - 2 * (-u₁) ^ 2 / (γ + 1) ^ 2| < ε := by sorry

end AstrophysicalFluidDynamics
