-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_einstein_static_collapse
-- name    : EinsteinStaticUniverse.einstein_static_collapse
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:26:21.210784+00:00
-- url     : https://prove2.me/theorems/503c7148-94f5-459f-ab91-b3e6f9aca921
-- title:
--   Instability, contracting side: $a(0)<a_E$ forces strict collapse
-- statement:
--   This is the contracting half of the instability of the Einstein static universe.
--
--   Let $G,\rho_0,a_0,a_E$ be positive, let $\Lambda=4\pi G\rho_0(a_0/a_E)^{3}$ be the Einstein balance value, and let $T>0$. Let $a$ be a twice differentiable function of time which is positive on $[0,T]$ and satisfies the acceleration equation
--   $$\ddot a(t)=-\frac{4\pi G}{3}\rho_0\left(\frac{a_0}{a(t)}\right)^{3}a(t)+\frac{\Lambda}{3}a(t)\qquad\text{for all }t\in[0,T],$$
--   with an inward initial displacement and no initial expansion:
--   $$a(0)<a_E,\qquad \dot a(0)\le0 .$$
--   Then $a$ is strictly decreasing on $[0,T]$.
--
--   Below the balance point the matter term dominates, the acceleration is strictly negative, and the contraction accelerates: a universe displaced inwards collapses. The conclusion is stated on a bounded time interval because a collapsing dust universe reaches zero scale factor in finite time, so no solution of this kind exists, positive, for all $t\ge 0$.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem einstein_static_collapse (G Λ ρ₀ a₀ aE T : ℝ) (hG : 0 < G) (hρ₀ : 0 < ρ₀)
    (ha₀ : 0 < a₀) (haE : 0 < aE) (hT : 0 < T)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) (a : ℝ → ℝ)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ a t)
    (hdiff₂ : ∀ t : ℝ, DifferentiableAt ℝ (deriv a) t)
    (hpos : ∀ t ∈ Set.Icc 0 T, 0 < a t)
    (heq : FriedmannII G Λ ρ₀ a₀ a (Set.Icc 0 T))
    (h₀ : a 0 < aE) (h₀' : deriv a 0 ≤ 0) :
    StrictAntiOn a (Set.Icc 0 T) := by sorry

end EinsteinStaticUniverse
