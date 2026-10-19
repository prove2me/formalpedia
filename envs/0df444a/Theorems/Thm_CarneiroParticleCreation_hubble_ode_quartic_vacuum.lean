-- Prove2me | Theorems.Thm_CarneiroParticleCreation_hubble_ode_quartic_vacuum
-- name    : CarneiroParticleCreation.hubble_ode_quartic_vacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:29:22.899061+00:00
-- url     : https://prove2.me/theorems/a4c12465-b523-492d-aa3f-6c48a34432bc
-- title:
--   Eq. (4): $\dot H + 2H^2 - 2H^4 = 0$ for $\Lambda = 3H^4$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open set of times, and let $H$, $\rho_m$, $\Lambda$ be real functions of time with $H$ differentiable at every $t\in I$. Assume that for all $t\in I$:
--
--   1. the vacuum law $\Lambda(t) = 3H(t)^4$;
--   2. the balance equation (2) with relativistic matter, $\dot\rho_m + 3H\left(\rho_m + \tfrac{\rho_m}{3}\right) = -\dot\Lambda$;
--   3. the Friedmann equation (3), $\rho_m + \Lambda = 3H^2$;
--   4. $H(t)\neq 0$.
--
--   Then for every $t\in I$,
--   $$\dot H + 2H^2 - 2H^4 = 0.$$
--
--   This is the evolution equation of the non-singular model recalled in the introduction of the paper.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 61, Eqs. (2)-(4)

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem hubble_ode_quartic_vacuum (I : Set ℝ) (hI : IsOpen I) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t)
    (hΛ : ∀ t ∈ I, Λ t = 3 * H t ^ 4)
    (h2 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = - deriv Λ t)
    (h3 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    ∀ t ∈ I, deriv H t + 2 * H t ^ 2 - 2 * H t ^ 4 = 0 := by sorry

end CarneiroParticleCreation
