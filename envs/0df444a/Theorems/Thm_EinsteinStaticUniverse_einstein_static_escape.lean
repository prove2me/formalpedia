-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_einstein_static_escape
-- name    : EinsteinStaticUniverse.einstein_static_escape
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:26:00.064742+00:00
-- url     : https://prove2.me/theorems/6babab6e-d702-4a26-b8a0-375975af98d0
-- title:
--   Instability, expanding side: $a(0)>a_E$ forces $a(t)\to\infty$
-- statement:
--   This is the expanding half of the instability of the Einstein static universe, stated for exact solutions rather than for the linearized equation.
--
--   Let $G,\rho_0,a_0,a_E$ be positive and let $\Lambda=4\pi G\rho_0(a_0/a_E)^{3}$ be the Einstein balance value. Let $a$ be a twice differentiable function of time satisfying the acceleration equation
--   $$\ddot a(t)=-\frac{4\pi G}{3}\rho_0\left(\frac{a_0}{a(t)}\right)^{3}a(t)+\frac{\Lambda}{3}a(t)\qquad\text{for all }t\ge0,$$
--   and suppose that at the initial time the universe is displaced outwards and not contracting:
--   $$a(0)>a_E,\qquad \dot a(0)\ge0 .$$
--   Then $a$ is strictly increasing on $[0,\infty)$ and
--   $$\lim_{t\to\infty}a(t)=+\infty .$$
--
--   No matter how small the outward displacement, the universe never returns: the repulsion of $\Lambda$ beats the diluting attraction of matter, and expansion runs away. This is the exact-solution form of the classical claim that Einstein's equilibrium releases vacuum energy when perturbed outwards.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem einstein_static_escape (G Λ ρ₀ a₀ aE : ℝ) (hG : 0 < G) (hρ₀ : 0 < ρ₀) (ha₀ : 0 < a₀)
    (haE : 0 < aE) (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) (a : ℝ → ℝ)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ a t)
    (hdiff₂ : ∀ t : ℝ, DifferentiableAt ℝ (deriv a) t)
    (heq : FriedmannII G Λ ρ₀ a₀ a (Set.Ici 0))
    (h₀ : aE < a 0) (h₀' : 0 ≤ deriv a 0) :
    StrictMonoOn a (Set.Ici 0) ∧ Filter.Tendsto a Filter.atTop Filter.atTop := by sorry

end EinsteinStaticUniverse
