-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_no_interior_radial_zero
-- name    : BirkhoffGlobalSection.left_negative_closure_no_interior_radial_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:07:24.697531+00:00
-- url     : https://prove2.me/theorems/4f901da0-8ee7-421b-b5f2-b1f6d422cd2b
-- title:
--   There are no earlier zero-energy points on an inner negative ray
-- statement:
--   For subcritical energy, no strict radial contraction of a point in the negative-component closure can have zero regularized Hamiltonian. Combined with nonpositive energy under contraction, this gives strict negativity before the outer boundary.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, star-shaped regularized component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_no_interior_radial_zero (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      ∀ a : ℝ, 0 ≤ a → a < 1 →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => a * s i) ≠ 0 := by sorry

end BirkhoffGlobalSection
