-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_closure_avoids_second_collision
-- name    : BirkhoffGlobalSection.left_component_closure_avoids_second_collision
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:29:45.340983+00:00
-- url     : https://prove2.me/theorems/72fabfc2-c293-4ddd-9299-deea03ea25db
-- title:
--   Closure of the left subcritical component avoids the second collision
-- statement:
--   For $0<\mu<1$ and energy $-c$ below the first critical value, every limit point of the selected connected component of the regular Levi-Civita energy level has strictly positive squared distance to the second collision. This is the geometric separation needed to keep the component inside the collision-free domain.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- A limit of points on the selected subcritical component cannot meet the
second collision, where Levi-Civita regularization is singular. -/
theorem left_component_closure_avoids_second_collision (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure (leftEnergyComponent μ c),
      0 < secondCollisionDistanceSq s := by sorry

end BirkhoffGlobalSection
