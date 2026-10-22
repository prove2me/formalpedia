-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_ray_unique_scale
-- name    : BirkhoffGlobalSection.left_component_ray_unique_scale
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T09:57:51.695985+00:00
-- url     : https://prove2.me/theorems/f9c096ac-8da4-49b0-b868-0a6d54e1ca2b
-- title:
--   Uniqueness of the positive intersection on each ray
-- statement:
--   For any unit phase direction $x\in S^3$, at most one positive radius reaches the selected subcritical energy component: if both $rx$ and $tx$ lie in that component with $r,t>0$, then $r=t$. This is the radial uniqueness part of the component geometry.
-- source:
--   Joung--van Koert, Birkhoff global sections for the planar circular restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (star-shaped regularized component).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_component_ray_unique_scale (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere, ∀ r t : ℝ,
      0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c →
      (fun i : Fin 4 => t * x i) ∈ leftEnergyComponent μ c →
      r = t := by sorry

end BirkhoffGlobalSection
