-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_radial_graph
-- name    : BirkhoffGlobalSection.left_negative_boundary_radial_graph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:16:18.799179+00:00
-- url     : https://prove2.me/theorems/2434040f-640f-431b-927f-4dc63efd3a28
-- title:
--   The inner zero boundary is a continuous radial graph
-- statement:
--   For a mass ratio between zero and one and an energy below the first critical value, the collision-free zero-energy boundary of the negative regularized-energy region connected to the origin is the radial graph of a strictly positive continuous function on the round unit three-sphere. This is the star-shaped geometry needed to identify the boundary as a connected hypersurface.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (the regularized component is star-shaped); standard topology of spheres.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_radial_graph (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ ρ : {x : Phase // x ∈ unitThreeSphere} → ℝ,
      Continuous ρ ∧
      (∀ x, 0 < ρ x) ∧
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} =
        Set.range (fun x : {x : Phase // x ∈ unitThreeSphere} =>
          (fun i : Fin 4 => ρ x * (x : Phase) i)) := by sorry

end BirkhoffGlobalSection
