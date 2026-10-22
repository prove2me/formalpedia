-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
-- name    : BirkhoffGlobalSection.left_component_position_radius_lt_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T08:17:14.008051+00:00
-- url     : https://prove2.me/theorems/57a9ce89-6241-4eaa-b86e-2b10a1bd6f87
-- title:
--   The left Hill component stays within the primary separation
-- statement:
--   For a subcritical energy in the planar circular restricted three-body problem, the selected connected component surrounding the left primary has its physical position uniformly inside a circle about that primary of squared radius strictly smaller than one. In the Levi-Civita variables, there is a constant $\rho<1$ such that every point $s$ of the component satisfies
--
--   $$|q(s)+(\mu,0)|^2\leq\rho.$$
--
--   Here the two primaries are one unit apart. This sharpened Hill-region bound separates the component from the right collision.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Section 2, geometry of subcritical Hill regions.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_component_position_radius_lt_one (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ s ∈ leftEnergyComponent μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
        ((leviCivitaPosition μ s) 1) ^ 2 ≤ ρ := by sorry

end BirkhoffGlobalSection
