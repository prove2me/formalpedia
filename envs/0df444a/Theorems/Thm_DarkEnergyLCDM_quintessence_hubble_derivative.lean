-- Prove2me | Theorems.Thm_DarkEnergyLCDM_quintessence_hubble_derivative
-- name    : DarkEnergyLCDM.quintessence_hubble_derivative
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:07:18.4418+00:00
-- url     : https://prove2.me/theorems/373f1a7a-cadb-4ceb-871d-60d3fceaeb41
-- title:
--   Quintessence: $\dot H = -4\pi G(\dot\phi^2+\rho+p)$
-- statement:
--   Let $I$ be an open interval, $G$ a constant, $a$ a $C^2$ function with $a>0$ on $I$, $\phi$ a $C^2$ function on $I$, $V$ a differentiable potential, and $\rho$ a matter density differentiable on $I$ with pressure $p$. Suppose that on $I$:
--
--   1. $H^2 = \frac{8\pi G}{3}\left(\frac{\dot\phi^2}{2} + V(\phi) + \rho\right)$ (Eq. 13);
--   2. $\ddot\phi + 3H\dot\phi + V'(\phi) = 0$ (Klein–Gordon, Eq. 15);
--   3. $\dot\rho + 3H(\rho+p) = 0$.
--
--   Then at every $t\in I$ with $H(t)\neq0$,
--   $$\dot H(t) = -4\pi G\left(\dot\phi(t)^2 + \rho(t) + p(t)\right).$$
--
--   This is the second Einstein equation (14) of the quintessence model.
--
--   **Formalization Note** The source prints $\dot H = -\frac{4\pi G}{3}(\dot\phi^2+\rho+p)$. That is inconsistent with (13) and (15) by a factor of $3$, and the consistent coefficient $-4\pi G$ is used here. Instants with $H=0$ are excluded because (14) is not a consequence of (13) and (15) there.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 71, Eqs. (13)–(15)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Real

theorem quintessence_hubble_derivative (G : ℝ) (I : Set ℝ) (hI : IsOpen I)
    (a ϕ V ρ p : ℝ → ℝ) (ha : ContDiffOn ℝ 2 a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hϕ : ContDiffOn ℝ 2 ϕ I) (hV : Differentiable ℝ V) (hρ : DifferentiableOn ℝ ρ I)
    (hfried : ∀ t ∈ I,
      hubble a t ^ 2 = 8 * π * G / 3 * (deriv ϕ t ^ 2 / 2 + V (ϕ t) + ρ t))
    (hKG : ∀ t ∈ I, deriv (deriv ϕ) t + 3 * hubble a t * deriv ϕ t + deriv V (ϕ t) = 0)
    (hcont : ∀ t ∈ I, ContinuityEq a ρ p t) :
    ∀ t ∈ I, hubble a t ≠ 0 →
      deriv (hubble a) t = -(4 * π * G) * (deriv ϕ t ^ 2 + ρ t + p t) := by sorry

end DarkEnergyLCDM
