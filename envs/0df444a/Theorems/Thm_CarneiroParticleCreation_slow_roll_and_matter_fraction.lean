-- Prove2me | Theorems.Thm_CarneiroParticleCreation_slow_roll_and_matter_fraction
-- name    : CarneiroParticleCreation.slow_roll_and_matter_fraction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:32:06.389872+00:00
-- url     : https://prove2.me/theorems/f9ca811b-6d23-4b69-8e66-044fd9bf6ca6
-- title:
--   Constant slow-roll parameter $\varepsilon = -\dot H/H^2$ and $\Omega_m = \varepsilon/2$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open set of times, let $\gamma\neq4$, and let $H,\rho_m,\Lambda$ be real functions with $H$ differentiable on $I$. Assume that for all $t\in I$: the balance equation (13) $\dot\rho_m + 3H(\rho_m+\rho_m/3)=\gamma H\rho_m$, the Friedmann equation (14) $\rho_m+\Lambda=3H^2$, the vacuum law (16) with $\Lambda_0=0$, $\Lambda = \tfrac{3\gamma}{4}H^2$, and $H(t)\neq0$. Put $\varepsilon = (4-\gamma)/2$. Then for every $t\in I$,
--   $$-\frac{\dot H(t)}{H(t)^2} = \varepsilon \qquad\text{and}\qquad \Omega_m(t)=\frac{\rho_m(t)}{3H(t)^2} = \frac{\varepsilon}{2}.$$
--
--   So the slow-roll parameter is constant along the inflationary solution, which the paper uses to get $n_s = 1-2\varepsilon$.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 64, text following Eqs. (17) and (18)

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem slow_roll_and_matter_fraction (I : Set ℝ) (hI : IsOpen I)
    (γ : ℝ) (hγ : γ ≠ 4) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t)
    (h13 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = γ * H t * ρm t)
    (h14 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (h16 : ∀ t ∈ I, Λ t = 3 * γ / 4 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    ∀ t ∈ I, - deriv H t / H t ^ 2 = (4 - γ) / 2 ∧
      ρm t / (3 * H t ^ 2) = ((4 - γ) / 2) / 2 := by sorry

end CarneiroParticleCreation
