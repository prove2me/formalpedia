-- Prove2me | Theorems.Thm_ConservationLaws_mechanical_energy_conservation
-- name    : ConservationLaws.mechanical_energy_conservation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:27.564083+00:00
-- url     : https://prove2.me/theorems/a236db2d-b618-4ff6-8c35-c500a4b667ba
-- title:
--   Conservation of mechanical energy in a conservative force field
-- statement:
--   A particle of mass $m > 0$ moves in $\mathbb{R}^d$ under a force derived from a differentiable potential $V : \mathbb{R}^d \to \mathbb{R}$, i.e. $m\,\ddot x(t) = -\nabla V(x(t))$. Then the mechanical energy
--   $$E(t) = \tfrac12 m\,\|\dot x(t)\|^2 + V(x(t))$$
--   is constant in time.
-- source:
--   Wikipedia, "Conservation of energy" (uploaded PDF), https://en.wikipedia.org/wiki/Conservation_of_energy, sections on kinetic and potential energy (vis viva, Galileo's interconversion of potential and kinetic energy); Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Relation to force"

import Mathlib

namespace ConservationLaws

theorem mechanical_energy_conservation
    {d : ℕ} (m : ℝ) (hm : 0 < m)
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (hV : Differentiable ℝ V)
    (x v a : ℝ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hnewton : ∀ t, m • a t = -gradient V (x t)) :
    ∀ t s, (1 / 2 : ℝ) * m * ‖v t‖ ^ 2 + V (x t) = (1 / 2 : ℝ) * m * ‖v s‖ ^ 2 + V (x s) := by sorry

end ConservationLaws
