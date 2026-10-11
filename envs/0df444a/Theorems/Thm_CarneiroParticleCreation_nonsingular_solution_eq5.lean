-- Prove2me | Theorems.Thm_CarneiroParticleCreation_nonsingular_solution_eq5
-- name    : CarneiroParticleCreation.nonsingular_solution_eq5
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:30:32.303981+00:00
-- url     : https://prove2.me/theorems/bf227b34-bec4-4545-8a1e-dc37a5f90280
-- title:
--   Eq. (5): the non-singular solution $2t = 1/H - \operatorname{artanh} H$
-- statement:
--   There is a function $H:\mathbb R\to\mathbb R$ such that:
--
--   1. $0 < H(t) < 1$ for every $t$;
--   2. $H$ satisfies the implicit relation (5)
--   $$2t = \frac{1}{H(t)} - \operatorname{artanh} H(t) \quad\text{for every } t;$$
--   3. $H$ is differentiable everywhere and solves Eq. (4), $\dot H(t) = -2H(t)^2 + 2H(t)^4$;
--   4. $H(t)\to 1$ (the de Sitter value) as $t\to-\infty$;
--   5. $H(t)\,t \to \tfrac12$ (a radiation phase) as $t\to+\infty$.
--
--   Since $h\mapsto 1/h - \operatorname{artanh} h$ is a bijection from $(0,1)$ onto $\mathbb R$, item 2 determines $H$ uniquely. The statement therefore says that this unique function is a smooth, everywhere-defined solution of Eq. (4) with the stated asymptotics.
-- source:
--   S. Carneiro, "Inflation driven by particle creation", AIP Conf. Proc. 1471 (2012) 61-65, https://doi.org/10.1063/1.4756813, p. 61, Eq. (5) and the following paragraph; Fig. 1

import Mathlib
open Filter Topology

namespace CarneiroParticleCreation

theorem nonsingular_solution_eq5 :
    ∃ H : ℝ → ℝ, (∀ t, 0 < H t ∧ H t < 1) ∧
      (∀ t, 2 * t = 1 / H t - Real.artanh (H t)) ∧
      (∀ t, HasDerivAt H (-2 * H t ^ 2 + 2 * H t ^ 4) t) ∧
      Tendsto H atBot (𝓝 1) ∧
      Tendsto (fun t => H t * t) atTop (𝓝 (1 / 2)) := by sorry

end CarneiroParticleCreation
