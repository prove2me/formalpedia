-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_ray_exists
-- name    : BirkhoffGlobalSection.left_component_ray_exists
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T09:57:39.782297+00:00
-- url     : https://prove2.me/theorems/c79e4a82-684d-4942-9ae0-73a081c838a7
-- title:
--   Existence of a positive intersection on every ray
-- statement:
--   At subcritical energy, every ray from the origin in four-dimensional Levi-Civita phase space meets the chosen energy component at some positive radius. Equivalently, for each unit vector $x\in S^3$ there is $r>0$ such that $rx$ belongs to the selected component. This is the radial existence part of its star-shaped geometry.
-- source:
--   Joung--van Koert, Birkhoff global sections for the planar circular restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (star-shaped regularized component).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_component_ray_exists (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧
      (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c := by sorry

end BirkhoffGlobalSection
