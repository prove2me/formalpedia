-- Prove2me | Theorems.Thm_CarneiroParticleCreation_inflaton_hubble_solution_eq23
-- name    : CarneiroParticleCreation.inflaton_hubble_solution_eq23
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:32:21.615082+00:00
-- url     : https://prove2.me/theorems/4e0136ef-7307-4c2d-aa5e-33e5772b055e
-- title:
--   Eq. (23): inflaton picture, $1/H = \varepsilon t + 1/H_0$ with $\varepsilon = \tfrac32\cdot\tfrac{4-\gamma}{2}$
-- statement:
--   Let $\gamma\in\mathbb R$. Let $H(\varphi)$ be a positive, everywhere differentiable function of the field $\varphi\in\mathbb R$, and let $V(\varphi)$ be the potential. Assume for every $\varphi$:
--
--   1. the field equation (21), $3H(\varphi)^2 = V(\varphi) + 2H'(\varphi)^2$;
--   2. $V(\varphi) = \tfrac{3\gamma}{4}H(\varphi)^2$.
--
--   Let $I\subseteq\mathbb R$ be an open, connected set of times and $\varphi(t)$ a trajectory, differentiable on $I$, satisfying the field equation (22) $\dot\varphi(t) = -2H'(\varphi(t))$ for $t\in I$. Then there is a constant $H_0$ such that
--   $$\frac{1}{H(\varphi(t))} = \varepsilon\, t + \frac{1}{H_0}\quad (t\in I),\qquad \varepsilon = \frac32\cdot\frac{4-\gamma}{2}.$$
--
--   Up to a rescaling of time, this reproduces the inflation solution (17) in the scalar-field description.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 64, Eqs. (21)-(23)

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem inflaton_hubble_solution_eq23 (γ : ℝ) (Hφ V : ℝ → ℝ)
    (hd : Differentiable ℝ Hφ) (hpos : ∀ φ, 0 < Hφ φ)
    (h21 : ∀ φ, 3 * Hφ φ ^ 2 = V φ + 2 * deriv Hφ φ ^ 2)
    (hV : ∀ φ, V φ = 3 * γ * Hφ φ ^ 2 / 4)
    (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ I, DifferentiableAt ℝ φ t)
    (h22 : ∀ t ∈ I, deriv φ t = -2 * deriv Hφ (φ t)) :
    ∃ H₀ : ℝ, ∀ t ∈ I, 1 / Hφ (φ t) = 3 / 2 * ((4 - γ) / 2) * t + 1 / H₀ := by sorry

end CarneiroParticleCreation
