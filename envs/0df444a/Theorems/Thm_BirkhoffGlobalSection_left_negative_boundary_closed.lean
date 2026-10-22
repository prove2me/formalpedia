-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_closed
-- name    : BirkhoffGlobalSection.left_negative_boundary_closed
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:31:08.374139+00:00
-- url     : https://prove2.me/theorems/c2b82fdc-6bda-4944-afad-5bf16b1843f3
-- title:
--   Closedness of the collision-free inner zero boundary
-- statement:
--   At subcritical energy, the collision-free zero-energy boundary of the negative regularized-energy region connected to the origin is closed in four-dimensional phase space. Separation from the second-collision singularity is essential for passing to limits.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_closed (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsClosed
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by sorry

end BirkhoffGlobalSection
