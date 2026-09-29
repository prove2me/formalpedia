-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_einstein_static_linearised
-- name    : EinsteinStaticUniverse.einstein_static_linearised
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:25:03.570816+00:00
-- url     : https://prove2.me/theorems/1e155ca0-afa8-40e7-9de6-4beca0e7dcb8
-- title:
--   Linearisation at the static point: $F'(a_E)=\Lambda$ and the growing mode $e^{\sqrt{\Lambda}t}$
-- statement:
--   Write the acceleration equation for dust plus $\Lambda$ as an autonomous second-order equation $\ddot a=F(a)$, with
--   $$F(x)=-\frac{4\pi G}{3}\rho_0\left(\frac{a_0}{x}\right)^{3}x+\frac{\Lambda}{3}x .$$
--   Let $G,\rho_0,a_0,a_E$ be positive and assume the Einstein balance $\Lambda=4\pi G\rho_0(a_0/a_E)^{3}$. Then
--
--   1. $\Lambda>0$;
--   2. $a_E$ is an equilibrium: $F(a_E)=0$;
--   3. $F$ is differentiable at $a_E$ with
--   $$F'(a_E)=\Lambda ;$$
--   4. the function $t\mapsto e^{\sqrt{\Lambda}\,t}$ satisfies $\ddot\delta=\Lambda\,\delta$.
--
--   Together these say that the linearization of the cosmological evolution at the static point is $\ddot\delta=\Lambda\delta$, whose characteristic exponents are $\pm\sqrt{\Lambda}$: a real growing mode with $e$-folding time $1/\sqrt{\Lambda}$ and a decaying mode. The positive exponent is the precise sense in which the static universe is linearly unstable, and it is the quantity that the nonlinear statements of this mission upgrade to a statement about exact solutions.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem einstein_static_linearised (G Λ ρ₀ a₀ aE : ℝ) (hG : 0 < G) (hρ₀ : 0 < ρ₀)
    (ha₀ : 0 < a₀) (haE : 0 < aE)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) :
    0 < Λ ∧ accel G Λ ρ₀ a₀ aE = 0 ∧ HasDerivAt (accel G Λ ρ₀ a₀) Λ aE ∧
      ∀ t : ℝ, deriv (deriv fun s : ℝ => Real.exp (Real.sqrt Λ * s)) t
        = Λ * Real.exp (Real.sqrt Λ * t) := by sorry

end EinsteinStaticUniverse
