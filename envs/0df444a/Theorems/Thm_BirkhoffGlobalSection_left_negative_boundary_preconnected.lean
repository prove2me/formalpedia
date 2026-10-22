-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_preconnected
-- name    : BirkhoffGlobalSection.left_negative_boundary_preconnected
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T12:39:00.170988+00:00
-- url     : https://prove2.me/theorems/a47ddec9-af4a-4428-8406-46a8f282900f
-- title:
--   Connected collision-free zero boundary of the inner negative-energy region
-- statement:
--   At an energy below the first critical value, consider the connected negative regularized-energy region containing the origin. The subset of its closure on which the Hamiltonian vanishes and the second collision is avoided is connected. This is the global geometric part of the boundary identification.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_preconnected (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsPreconnected
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by sorry

end BirkhoffGlobalSection
