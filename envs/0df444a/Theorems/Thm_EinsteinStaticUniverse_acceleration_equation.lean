-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_acceleration_equation
-- name    : EinsteinStaticUniverse.acceleration_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:22:48.403359+00:00
-- url     : https://prove2.me/theorems/71f16904-e48e-488f-8478-038f5cd224a7
-- title:
--   The acceleration equation follows from the first Friedmann equation
-- statement:
--   The second Friedmann equation is not an independent postulate: along any solution of the first one whose expansion rate does not vanish, it follows by differentiation. Let $a$ be a scale factor defined on an open set of times $I$, positive there, twice differentiable there, with $\dot a(t)\neq0$ for all $t\in I$, and satisfying
--   $$\dot a^{2}=\frac{8\pi G}{3}\rho_0\left(\frac{a_0}{a}\right)^{3}a^{2}-k+\frac{\Lambda}{3}a^{2}$$
--   on $I$. Then on $I$,
--   $$\ddot a=-\frac{4\pi G}{3}\rho_0\left(\frac{a_0}{a}\right)^{3}a+\frac{\Lambda}{3}a .$$
--
--   The curvature constant $k$ disappears: it is the constant of integration of the first equation, so it cannot appear in the second. The hypothesis $\dot a\neq0$ is exactly what is needed to divide by $\dot a$ after differentiating, and it is the reason the static solution — where $\dot a\equiv0$ — has to be treated separately.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem acceleration_equation (G Λ k ρ₀ a₀ : ℝ) (a : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hpos : ∀ t ∈ I, 0 < a t) (hne : ∀ t ∈ I, deriv a t ≠ 0)
    (hdiff : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (hdiff₂ : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t)
    (h : FriedmannI G Λ k ρ₀ a₀ a I) :
    FriedmannII G Λ ρ₀ a₀ a I := by sorry

end EinsteinStaticUniverse
