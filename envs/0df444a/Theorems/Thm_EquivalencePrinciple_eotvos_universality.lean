-- Prove2me | Theorems.Thm_EquivalencePrinciple_eotvos_universality
-- name    : EquivalencePrinciple.eotvos_universality
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T00:56:47.918056+00:00
-- url     : https://prove2.me/theorems/5e1b4217-2b46-589d-b7a4-60ff489ee10b
-- title:
--   Weak equivalence principle: universality of free fall (Newtonian form)
-- statement:
--   **The weak equivalence principle, Newtonian form — universality of free fall.**
--
--   Let `G : Vec3 → Vec3` be a gravitational field (a continuously differentiable vector field — the acceleration field of some potential), and let `A`, `B` be two falling test bodies in `G`: each with positive passive gravitational mass `mg` and positive inertial mass `mi`, a twice continuously differentiable trajectory, obeying
--
--   $$x''(t) \;=\; \tfrac{m_g}{m_i}\, G(x(t)) \quad \text{for every } t.$$
--
--   Assume the two bodies have **equal mass ratios** ($m_g/m_i$ of `A` equals $m_g/m_i$ of `B`; the Eötvös ratio $\eta(A,B) = 0$ — in particular this holds when both bodies have $m_g = m_i$, the empirical content of the Eötvös experiments), and that they are **launched alike**: same initial position and same initial velocity at time $t_0$.
--
--   **Conclusion:** the trajectories coincide for all time: $A.x\, t = B.x\, t$ for every $t$.
--
--   In words: all bodies with the same mass ratio falling in the same gravitational field from the same place with the same velocity follow the same path regardless of their composition — "in a gravitational field the acceleration of a test particle is independent of its properties, including its rest mass." Formally the two bodies solve the same differential equation with the same initial data, and the conclusion is uniqueness of ODE solutions.
--
--   **Formalization note.** The field is carried as the acceleration field directly (the potential is not needed); the hypothesis that the field is `C¹` makes the right-hand side locally Lipschitz, which is what ODE uniqueness requires. The statement is global in time; this is true by the standard continuation argument.
-- source:
--   Wikipedia, Equivalence principle, https://en.wikipedia.org/wiki/Equivalence_principle (source of the quoted statements, reproduced verbatim in the definition file) (weak equivalence principle; 'inertial mass x acceleration = gravitational mass x gravitational acceleration'; Eotvos ratio); L. Eotvos (1889), torsion-balance experiments

import Mathlib
import Definitions.Def_EquivalencePrinciple

namespace EquivalencePrinciple

/-- Milestone: the weak equivalence principle in its Newtonian form — the
universality of free fall.  Two falling test bodies in the same gravitational
field, with equal ratios of passive gravitational to inertial mass (in
particular with `m_g = m_i` for both, the empirical content of the Eötvös
experiments, i.e. Eötvös ratio zero), launched from the same place with the
same velocity, have the same trajectory for all time: the fall equation
`x'' = (mg/mi) • G (x)` involves the bodies' properties only through the mass
ratio, so with equal ratios the two bodies solve the same differential equation
with the same initial data. -/
theorem eotvos_universality (G : Vec3 → Vec3) (hG : IsGravField G)
    (A B : FallingBody G) (t₀ : ℝ) (hratio : A.mg / A.mi = B.mg / B.mi)
    (hlaunch : SameLaunch A B t₀) : ∀ t : ℝ, A.x t = B.x t := by
  sorry

end EquivalencePrinciple
