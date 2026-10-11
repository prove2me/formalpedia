-- Prove2me | Theorems.Thm_CarneiroParticleCreation_late_time_vacuum_law_eq10
-- name    : CarneiroParticleCreation.late_time_vacuum_law_eq10
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:30:46.083973+00:00
-- url     : https://prove2.me/theorems/897f9936-67f9-4494-98b0-9d0dd4efcc49
-- title:
--   Eq. (10): late-time vacuum law $\Lambda = 2\Gamma H + \lambda_0$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open, connected set of times, let $\Gamma\in\mathbb R$ be a constant creation rate, and let $H,\rho_m,\Lambda$ be real functions of time with $H$ and $\rho_m$ differentiable on $I$. Assume that for all $t\in I$:
--
--   1. the balance equation (7), $\dot\rho_m + 3H\rho_m = \Gamma\rho_m$;
--   2. the Friedmann equation (8), $\rho_m + \Lambda = 3H^2$;
--   3. $H(t)\neq 0$ and $3H(t)\neq\Gamma$.
--
--   With total density $\rho=\rho_m+\Lambda$ and total pressure $p=-\Lambda$ (dust plus vacuum), the following are equivalent:
--
--   - conservation of total energy (9), $\dot\rho + 3H(\rho+p) = 0$ on $I$;
--   - there is a constant $\lambda_0$ with
--   $$\Lambda(t) = 2\Gamma H(t) + \lambda_0 \quad\text{for all } t\in I.$$
--
--   **Formalization Note** The condition $3H\neq\Gamma$ is not stated in the paper. It is needed for the implication (10) $\Rightarrow$ (9): if $H\equiv\Gamma/3$ is constant, then (7), (8) and (10) hold but (9) fails whenever $\Gamma\rho_m\neq0$.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 62, Eqs. (7)-(10)

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem late_time_vacuum_law_eq10 (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (Γ : ℝ) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hρ : ∀ t ∈ I, DifferentiableAt ℝ ρm t)
    (h7 : ∀ t ∈ I, deriv ρm t + 3 * H t * ρm t = Γ * ρm t)
    (h8 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) (hΓ : ∀ t ∈ I, 3 * H t ≠ Γ) :
    (∀ t ∈ I, deriv (fun s => ρm s + Λ s) t + 3 * H t * ((ρm t + Λ t) + (- Λ t)) = 0) ↔
      ∃ lam₀ : ℝ, ∀ t ∈ I, Λ t = 2 * Γ * H t + lam₀ := by sorry

end CarneiroParticleCreation
