-- Prove2me | Theorems.Thm_CarneiroParticleCreation_inflation_solution
-- name    : CarneiroParticleCreation.inflation_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:33:22.051258+00:00
-- url     : https://prove2.me/theorems/6edb5dd6-9ffb-4556-8fb0-ea0a32ecaf02
-- title:
--   Eq. (17): inflation from relativistic particle creation, $1/H = \varepsilon t + 1/H_0$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open, connected set of times, let $\gamma\neq4$ be a constant, and let $H,\rho_m,\Lambda$ be real functions of time with $H$ differentiable at every point of $I$. Assume that for all $t\in I$:
--
--   1. the balance equation (13) for relativistic matter ($p_m=\rho_m/3$) created at rate $\gamma H$:
--   $$\dot\rho_m + 3H\left(\rho_m + \frac{\rho_m}{3}\right) = \gamma H\rho_m;$$
--   2. the Friedmann equation (14), $\rho_m + \Lambda = 3H^2$;
--   3. the vacuum law (16) with $\Lambda_0 = 0$, $\Lambda = \tfrac{3\gamma}{4}H^2$;
--   4. $H(t)\neq 0$.
--
--   Then there is an integration constant $H_0$ such that
--   $$\frac{1}{H(t)} = \varepsilon\, t + \frac{1}{H_0}\quad\text{for all } t\in I,\qquad \varepsilon = \frac{4-\gamma}{2}.$$
--
--   This is the paper's inflationary solution. For $\gamma\approx4$ one has $\varepsilon\ll1$ and $H\approx H_0$, a quasi-de Sitter phase with constant slow-roll parameter.
--
--   **Formalization Note** $I$ is an interval rather than all of $\mathbb R$ because $1/H$ vanishes at a finite time, so no solution with $H\neq0$ exists for all times when $\varepsilon\neq0$. $H_0$ enters only through $1/H_0$, so (with $1/0=0$ in Lean) the claim is that $1/H - \varepsilon t$ is constant on $I$.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 64, Eq. (17), from Eqs. (13), (14), (16) with Λ₀ = 0

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem inflation_solution (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (γ : ℝ) (hγ : γ ≠ 4) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t)
    (h13 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = γ * H t * ρm t)
    (h14 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (h16 : ∀ t ∈ I, Λ t = 3 * γ / 4 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    ∃ H₀ : ℝ, ∀ t ∈ I, 1 / H t = (4 - γ) / 2 * t + 1 / H₀ := by sorry

end CarneiroParticleCreation
