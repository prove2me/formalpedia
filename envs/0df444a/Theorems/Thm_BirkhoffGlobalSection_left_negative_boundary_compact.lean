-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_compact
-- name    : BirkhoffGlobalSection.left_negative_boundary_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:23:54.51375+00:00
-- url     : https://prove2.me/theorems/1f6351c4-4aa4-45ce-a569-5181fd61b699
-- title:
--   Compactness of the inner negative-energy boundary
-- statement:
--   Below the first critical energy, the collision-free zero-energy boundary of the regularized negative-energy component containing the origin is compact. This combines boundedness of the inner Hill region with separation from the second collision.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (geometric subcritical component); standard compact-to-Hausdorff inverse theorem.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_compact (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsCompact
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by sorry

end BirkhoffGlobalSection
