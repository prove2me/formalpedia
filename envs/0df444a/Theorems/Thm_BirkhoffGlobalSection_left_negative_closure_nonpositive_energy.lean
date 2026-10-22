-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_nonpositive_energy
-- name    : BirkhoffGlobalSection.left_negative_closure_nonpositive_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:06:38.153633+00:00
-- url     : https://prove2.me/theorems/9d460a80-ecf7-4179-b871-0a25fb86e209
-- title:
--   Nonpositive energy on the closure of the inner negative component
-- statement:
--   At subcritical energy, continuity of the regularized Hamiltonian away from the second collision carries its strict negativity on the origin component to a nonpositive bound on that component closure.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Equation (2.2), Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_nonpositive_energy (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))),
      leviCivitaHamiltonian μ c s ≤ 0 := by sorry

end BirkhoffGlobalSection
