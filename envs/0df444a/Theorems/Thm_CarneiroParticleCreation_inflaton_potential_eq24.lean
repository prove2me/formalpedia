-- Prove2me | Theorems.Thm_CarneiroParticleCreation_inflaton_potential_eq24
-- name    : CarneiroParticleCreation.inflaton_potential_eq24
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:32:35.000306+00:00
-- url     : https://prove2.me/theorems/6dbe9935-c32e-4ea6-be41-046d8acd6c70
-- title:
--   Eq. (24): exponential inflaton potential and $V''/V = (V'/V)^2 = 2\varepsilon$
-- statement:
--   Let $0<\gamma<4$ and put $\varepsilon = \tfrac32\cdot\tfrac{4-\gamma}{2}$. Let $H(\varphi)$ be a positive, everywhere differentiable function of $\varphi\in\mathbb R$, and let $V$ be a real function. Assume for every $\varphi$ the field equation (21) $3H^2 = V + 2H'^2$ and $V = \tfrac{3\gamma}{4}H^2$. Then:
--
--   1. there is a sign $s\in\{+1,-1\}$ such that, with $H_0 = H(0)$,
--   $$V(\varphi) = \frac{3\gamma H_0^2}{4}\,e^{s\sqrt{2\varepsilon}\,\varphi}\quad\text{for all }\varphi;$$
--   2. for every $\varphi$,
--   $$\frac{V''(\varphi)}{V(\varphi)} = 2\varepsilon \qquad\text{and}\qquad \left(\frac{V'(\varphi)}{V(\varphi)}\right)^2 = 2\varepsilon.$$
--
--   These are the slow-roll conditions the paper uses to conclude scale invariance when $\varepsilon\ll1$.
--
--   **Formalization Note** The sign $s$ is the same for all $\varphi$. This is part of the claim, not an assumption.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 64, Eq. (24) and the following paragraph

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem inflaton_potential_eq24 (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 4) (Hφ V : ℝ → ℝ)
    (hd : Differentiable ℝ Hφ) (hpos : ∀ φ, 0 < Hφ φ)
    (h21 : ∀ φ, 3 * Hφ φ ^ 2 = V φ + 2 * deriv Hφ φ ^ 2)
    (hV : ∀ φ, V φ = 3 * γ * Hφ φ ^ 2 / 4) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ φ, V φ =
        3 * γ * Hφ 0 ^ 2 / 4 * Real.exp (s * Real.sqrt (2 * (3 / 2 * ((4 - γ) / 2))) * φ)) ∧
    ∀ φ, deriv (deriv V) φ / V φ = 2 * (3 / 2 * ((4 - γ) / 2)) ∧
      (deriv V φ / V φ) ^ 2 = 2 * (3 / 2 * ((4 - γ) / 2)) := by sorry

end CarneiroParticleCreation
