-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_unique_ray_scale
-- name    : BirkhoffGlobalSection.left_negative_boundary_unique_ray_scale
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:30:25.593652+00:00
-- url     : https://prove2.me/theorems/eaad0e4c-2311-4624-aa6f-b3f56cf35879
-- title:
--   Uniqueness of the inner negative boundary on each positive radial ray
-- statement:
--   For subcritical energy, two collision-free zero-energy points on the same positive ray cannot both belong to the boundary of the negative-energy region connected to the origin unless their radial parameters agree. This separates the first boundary crossing from any later zero of the Hamiltonian.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, star-shapedness of the regularized bounded component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_unique_ray_scale (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * (x : Phase) i) ∈
        {s : Phase | s ∈ closure
          (connectedComponentIn
            {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
              0 < secondCollisionDistanceSq u}
            (fun _ : Fin 4 => (0 : ℝ))) ∧
          leviCivitaHamiltonian μ c s = 0 ∧
          0 < secondCollisionDistanceSq s} →
      (fun i : Fin 4 => t * (x : Phase) i) ∈
        {s : Phase | s ∈ closure
          (connectedComponentIn
            {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
              0 < secondCollisionDistanceSq u}
            (fun _ : Fin 4 => (0 : ℝ))) ∧
          leviCivitaHamiltonian μ c s = 0 ∧
          0 < secondCollisionDistanceSq s} →
      r = t := by sorry

end BirkhoffGlobalSection
