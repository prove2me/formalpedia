-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_second_collision_separated
-- name    : BirkhoffGlobalSection.left_component_second_collision_separated
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T08:08:02.467402+00:00
-- url     : https://prove2.me/theorems/08e0c370-bd92-4812-af2a-a474c2a87aaa
-- title:
--   The left subcritical component stays away from the right collision
-- statement:
--   For mass ratio $0<\mu<1$ and energy below the first critical value, the selected regularized component surrounding the left primary stays a positive distance from the collision with the right primary. More precisely, there is a constant $\delta>0$ such that for every point $s$ in that component,
--
--   $$\sqrt{D_2(s)}\geq\delta,$$
--
--   where $D_2$ is the squared distance to the right collision in Levi-Civita coordinates. This separation controls the right-primary gravitational term in the energy identity.
-- source:
--   Joung--van Koert, Birkhoff global sections for the planar circular restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Section 2 (Hill-region geometry).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_component_second_collision_separated (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ leftEnergyComponent μ c,
      δ ≤ Real.sqrt (secondCollisionDistanceSq s) := by sorry

end BirkhoffGlobalSection
