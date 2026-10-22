-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_bounded
-- name    : BirkhoffGlobalSection.left_negative_closure_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:42:42.882185+00:00
-- url     : https://prove2.me/theorems/9d4f47f5-5e23-4d82-9862-599913ddb526
-- title:
--   Boundedness of the inner negative-energy closure
-- statement:
--   The closure of the collision-free negative regularized-energy region containing the origin is bounded at subcritical energy. The inner Hill barrier bounds position, and the Hamiltonian inequality bounds momentum away from the second collision.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region separation.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    Bornology.IsBounded
      (closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ)))) := by sorry

end BirkhoffGlobalSection
