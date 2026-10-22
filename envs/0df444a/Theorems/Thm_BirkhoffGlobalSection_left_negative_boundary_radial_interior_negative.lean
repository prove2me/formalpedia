-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_radial_interior_negative
-- name    : BirkhoffGlobalSection.left_negative_boundary_radial_interior_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:42:46.423533+00:00
-- url     : https://prove2.me/theorems/deef465d-5fda-4124-90aa-7a910b393faf
-- title:
--   Energy is negative inside every inner boundary ray
-- statement:
--   For every collision-free zero-energy point on the boundary of the origin negative-energy component, the regularized Hamiltonian remains strictly negative at every earlier point of the same nonnegative radial segment. This strengthens ordinary boundary membership to the radial star-shaped property.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region separation.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_radial_interior_negative (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∀ r : ℝ, 0 < r →
      (fun i : Fin 4 => r * (x : Phase) i) ∈
        {s : Phase | s ∈ closure
          (connectedComponentIn
            {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
              0 < secondCollisionDistanceSq u}
            (fun _ : Fin 4 => (0 : ℝ))) ∧
          leviCivitaHamiltonian μ c s = 0 ∧
          0 < secondCollisionDistanceSq s} →
      ∀ t : ℝ, 0 ≤ t → t < r →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => t * (x : Phase) i) < 0 := by sorry

end BirkhoffGlobalSection
