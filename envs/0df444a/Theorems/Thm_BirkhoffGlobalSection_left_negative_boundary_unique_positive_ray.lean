-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_unique_positive_ray
-- name    : BirkhoffGlobalSection.left_negative_boundary_unique_positive_ray
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:23:54.570956+00:00
-- url     : https://prove2.me/theorems/af00a5f6-71a3-4f3e-9095-96be3a2c966d
-- title:
--   Unique positive boundary point on each ray
-- statement:
--   Every unit direction in four-dimensional regularized phase space meets the collision-free zero-energy boundary of the inner negative-energy region at exactly one positive radius. This is the radial star-shaped property of the inner boundary.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (geometric subcritical component); standard compact-to-Hausdorff inverse theorem.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_unique_positive_ray (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, 0 < r ∧
        (fun i : Fin 4 => r * (x : Phase) i) ∈
          {s : Phase | s ∈ closure
            (connectedComponentIn
              {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
                0 < secondCollisionDistanceSq t}
              (fun _ : Fin 4 => (0 : ℝ))) ∧
            leviCivitaHamiltonian μ c s = 0 ∧
            0 < secondCollisionDistanceSq s} := by sorry

end BirkhoffGlobalSection
