-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_strict_radial_star_shaped
-- name    : BirkhoffGlobalSection.left_negative_closure_strict_radial_star_shaped
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:00:39.633105+00:00
-- url     : https://prove2.me/theorems/3bfe0a04-a391-4574-ae7b-2b5b234e6a18
-- title:
--   Strict radial star-shapedness of the inner negative-energy closure
-- statement:
--   At subcritical energy, every point in the closure of the origin negative-energy component has strictly negative regularized Hamiltonian at every earlier nonnegative radial multiple. This is the strong star-shapedness estimate from which uniqueness of a zero-energy boundary intersection follows.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, star-shaped regularized component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_strict_radial_star_shaped (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      ∀ a : ℝ, 0 ≤ a → a < 1 →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => a * s i) < 0 := by sorry

end BirkhoffGlobalSection
