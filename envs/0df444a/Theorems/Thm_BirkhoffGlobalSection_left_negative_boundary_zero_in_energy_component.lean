-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_zero_in_energy_component
-- name    : BirkhoffGlobalSection.left_negative_boundary_zero_in_energy_component
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T12:28:52.725077+00:00
-- url     : https://prove2.me/theorems/c9546c89-7fce-4de9-9f76-199f2ff23364
-- title:
--   The collision-free boundary of the inner negative region is the left component
-- statement:
--   For subcritical energy, a collision-free zero of the Levi-Civita Hamiltonian lying on the boundary of the negative-energy region connected to the origin belongs to the selected regularized energy component around the left primary. This is the global Hill-region identification that distinguishes the inner boundary from outer zero-energy components.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region description.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_boundary_zero_in_energy_component (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))),
      leviCivitaHamiltonian μ c s = 0 →
      0 < secondCollisionDistanceSq s →
      s ∈ leftEnergyComponent μ c := by sorry

end BirkhoffGlobalSection
