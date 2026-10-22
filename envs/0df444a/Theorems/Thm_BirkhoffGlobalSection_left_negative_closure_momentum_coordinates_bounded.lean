-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_momentum_coordinates_bounded
-- name    : BirkhoffGlobalSection.left_negative_closure_momentum_coordinates_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:59:25.739559+00:00
-- url     : https://prove2.me/theorems/a0b482a9-21f0-4814-ab8f-272daca3f375
-- title:
--   Bounded momentum coordinates in the inner negative component
-- statement:
--   Below the first critical value, the two Levi-Civita momentum coordinates remain uniformly bounded on the closure of the origin negative-energy component. The regularized energy inequality, bounded position, and separation from the second collision supply the estimate.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and subcritical Hill-region bounds.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_momentum_coordinates_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ R : ℝ, ∀ s ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))),
      |s 2| ≤ R ∧ |s 3| ≤ R := by sorry

end BirkhoffGlobalSection
