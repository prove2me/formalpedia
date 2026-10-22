-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_bounded
-- name    : BirkhoffGlobalSection.left_negative_boundary_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:31:00.694595+00:00
-- url     : https://prove2.me/theorems/a28cc998-692b-4744-a797-c1a66c35498c
-- title:
--   Boundedness of the collision-free inner zero boundary
-- statement:
--   At subcritical energy, the collision-free zero-energy boundary of the negative regularized-energy region connected to the origin is bounded in regularized phase space. This is the bounded Hill-component estimate, including control of momentum coordinates.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    Bornology.IsBounded
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by sorry

end BirkhoffGlobalSection
