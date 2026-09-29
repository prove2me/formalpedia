-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_omega_sum_eq_one
-- name    : EinsteinStaticUniverse.omega_sum_eq_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:21:44.789813+00:00
-- url     : https://prove2.me/theorems/5c5b657f-026f-48a3-84c7-5592e3306357
-- title:
--   The density parameters satisfy $\Omega_m+\Omega_k+\Omega_\Lambda=1$
-- statement:
--   The Friedmann equation is equivalent to a normalization condition on dimensionless density parameters. Suppose the first Friedmann equation for dust holds on a set of times $I$, with Newton constant $G>0$, cosmological constant $\Lambda$ and curvature constant $k$. Fix a time $t\in I$ at which the scale factor and the Hubble parameter $H=\dot a(t)/a(t)$ are both nonzero. Writing $\rho_c=3H^{2}/(8\pi G)$ for the critical density and
--   $$\Omega_m=\frac{\rho}{\rho_c},\qquad \Omega_k=-\frac{k}{a^{2}H^{2}},\qquad \Omega_\Lambda=\frac{\Lambda}{3H^{2}},$$
--   all evaluated at that time, one has
--   $$\Omega_m+\Omega_k+\Omega_\Lambda=1 .$$
--
--   This identity is the bookkeeping behind statements such as "the universe is flat and about $70\%$ dark energy": flatness is $\Omega_k=0$, and the remaining parameters must then sum to one at every instant.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem omega_sum_eq_one (G Λ k ρ₀ a₀ : ℝ) (hG : 0 < G) (a : ℝ → ℝ) (I : Set ℝ)
    (h : FriedmannI G Λ k ρ₀ a₀ a I) (t : ℝ) (ht : t ∈ I) (ha : a t ≠ 0)
    (hH : hubbleParameter a t ≠ 0) :
    omegaM G (hubbleParameter a t) (dustDensity ρ₀ a₀ (a t))
        + omegaK k (a t) (hubbleParameter a t)
        + omegaLambda Λ (hubbleParameter a t) = 1 := by sorry

end EinsteinStaticUniverse
