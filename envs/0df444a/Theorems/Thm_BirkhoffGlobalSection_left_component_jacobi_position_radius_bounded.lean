-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_jacobi_position_radius_bounded
-- name    : BirkhoffGlobalSection.left_component_jacobi_position_radius_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:36:17.655987+00:00
-- url     : https://prove2.me/theorems/a7d2a941-78ad-49e0-83fd-f683edf4e5c2
-- title:
--   Bounded Jacobi position radius of the selected subcritical component
-- statement:
--   Let $0<\mu<1$ and let the energy $-c$ lie below the first critical value. For every point of the selected connected component of the regular Levi–Civita energy level, map its regularized position back to the Jacobi position $q$. There is a constant $R_q$ such that the squared distance $|q+\mu|^2$ from the left primary is at most $R_q$ for every such point. This is the physical-space Hill-region confinement needed to bound regularized position coordinates.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The projection of the selected subcritical component to physical Jacobi
position stays within a bounded distance of the left primary. -/
theorem left_component_jacobi_position_radius_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ Rq : ℝ, ∀ s ∈ leftEnergyComponent μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
        ((leviCivitaPosition μ s) 1) ^ 2 ≤ Rq := by sorry

end BirkhoffGlobalSection
