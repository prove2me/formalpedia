-- Prove2me | Theorems.Thm_ConservationLaws_total_mass_conserved_of_continuity_equation
-- name    : ConservationLaws.total_mass_conserved_of_continuity_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:35.357195+00:00
-- url     : https://prove2.me/theorems/f67c5229-526a-4a67-8770-e86092e3a979
-- title:
--   Continuity equation ⇒ total mass is conserved
-- statement:
--   Let $\rho(t,x)$ be a mass density and $u(t,x)$ a velocity field on $\mathbb{R}^n$, both continuously differentiable in $(t,x)$, with $\rho(t,\cdot)$ vanishing outside a fixed ball for all $t$. If the continuity equation
--   $$\frac{\partial \rho}{\partial t} + \nabla\cdot(\rho\,u) = 0$$
--   holds everywhere, then the total mass $\int_{\mathbb{R}^n}\rho(t,x)\,dx$ does not depend on $t$.
-- source:
--   Wikipedia, "Conservation of mass" (uploaded PDF), https://en.wikipedia.org/wiki/Conservation_of_mass, section "Formulation and examples" (continuity equation in differential form and $dM/dt = 0$ for the whole isolated system)

import Mathlib

namespace ConservationLaws

theorem total_mass_conserved_of_continuity_equation
    {n : ℕ} (ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hρ : ContDiff ℝ 1 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => ρ p.1 p.2))
    (hu : ContDiff ℝ 1 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hsupp : ∃ R : ℝ, ∀ t x, R < ‖x‖ → ρ t x = 0)
    (hcont : ∀ t x, deriv (fun s => ρ s x) t +
      ∑ k : Fin n, fderiv ℝ (fun y => ρ t y * u t y k) x (EuclideanSpace.single k 1) = 0) :
    ∀ t s, ∫ x, ρ t x = ∫ x, ρ s x := by sorry

end ConservationLaws
