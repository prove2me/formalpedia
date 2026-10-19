-- Prove2me | Theorems.Thm_CarneiroParticleCreation_early_time_vacuum_law_eq16
-- name    : CarneiroParticleCreation.early_time_vacuum_law_eq16
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:31:39.882989+00:00
-- url     : https://prove2.me/theorems/9c64125c-1f43-4181-94bc-7f6fea958eaa
-- title:
--   Eq. (16): early-time vacuum law $\Lambda = \tfrac{3\gamma}{4}H^2 + \Lambda_0$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open, connected set of times, let $\gamma\neq4$ be a constant, and let $H,\rho_m,\Lambda$ be real functions of time with $H$ and $\rho_m$ differentiable on $I$. Assume that for all $t\in I$:
--
--   1. the balance equation (13) for relativistic matter, $\dot\rho_m + 3H\left(\rho_m+\tfrac{\rho_m}{3}\right) = \gamma H\rho_m$;
--   2. the Friedmann equation (14), $\rho_m+\Lambda=3H^2$;
--   3. $H(t)\neq0$.
--
--   With $\rho=\rho_m+\Lambda$ and $p=\rho_m/3-\Lambda$, the following are equivalent:
--
--   - conservation of total energy (15), $\dot\rho+3H(\rho+p)=0$ on $I$;
--   - there is a constant $\Lambda_0$ with
--   $$\Lambda(t) = \frac{3\gamma}{4}H(t)^2 + \Lambda_0\quad\text{for all } t\in I.$$
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 63, Eqs. (13)-(16)

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem early_time_vacuum_law_eq16 (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (γ : ℝ) (hγ : γ ≠ 4) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hρ : ∀ t ∈ I, DifferentiableAt ℝ ρm t)
    (h13 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = γ * H t * ρm t)
    (h14 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    (∀ t ∈ I, deriv (fun s => ρm s + Λ s) t +
        3 * H t * ((ρm t + Λ t) + (ρm t / 3 - Λ t)) = 0) ↔
      ∃ Λ₀ : ℝ, ∀ t ∈ I, Λ t = 3 * γ / 4 * H t ^ 2 + Λ₀ := by sorry

end CarneiroParticleCreation
