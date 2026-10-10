-- Prove2me | Theorems.Thm_ConservationLaws_work_energy_theorem
-- name    : ConservationLaws.work_energy_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:45.760974+00:00
-- url     : https://prove2.me/theorems/e00dce01-2bca-4c46-b70c-42beaabc896c
-- title:
--   Work–energy theorem: $\Delta(\tfrac12 m\|v\|^2) = \int \langle F, v\rangle\,dt$
-- statement:
--   A particle of mass $m > 0$ moves in $\mathbb{R}^d$ under a continuous time-dependent force $F(t)$, with $m\,\ddot x(t) = F(t)$. Then for all times $t_0, t_1$,
--   $$\tfrac12 m\|v(t_1)\|^2 - \tfrac12 m\|v(t_0)\|^2 = \int_{t_0}^{t_1} \langle F(t), v(t)\rangle\,dt,$$
--   i.e. the change in kinetic energy equals the work done by the force.
-- source:
--   Wikipedia, "Conservation of energy" (uploaded PDF), https://en.wikipedia.org/wiki/Conservation_of_energy (energy transferred as work); Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Relation to force" (Newton's second law $F = m a$)

import Mathlib

namespace ConservationLaws

theorem work_energy_theorem
    {d : ℕ} (m : ℝ) (hm : 0 < m)
    (F : ℝ → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (x v a : ℝ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hnewton : ∀ t, m • a t = F t) :
    ∀ t₀ t₁, (1 / 2 : ℝ) * m * ‖v t₁‖ ^ 2 - (1 / 2 : ℝ) * m * ‖v t₀‖ ^ 2 =
      ∫ t in t₀..t₁, inner ℝ (F t) (v t) := by sorry

end ConservationLaws
