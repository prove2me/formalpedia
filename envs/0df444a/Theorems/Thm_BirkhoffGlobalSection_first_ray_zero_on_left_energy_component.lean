-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_first_ray_zero_on_left_energy_component
-- name    : BirkhoffGlobalSection.first_ray_zero_on_left_energy_component
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:22:32.895775+00:00
-- url     : https://prove2.me/theorems/8a01505f-bb06-4c27-9791-7df6a8faf7e0
-- title:
--   The first radial zero lies on the left energy component
-- statement:
--   A collision-free first zero of regularized energy along a ray from the negative-energy origin belongs to the selected zero-energy component based at the left-primary collision. The strict negativity at every earlier radius selects the boundary of the inner Hill region and excludes an outer zero-energy branch. This is the component-identification step in the radial existence argument.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and equation (2.2), radial energy and Hill-region component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem first_ray_zero_on_left_energy_component (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (x : Phase) (hx : x ∈ unitThreeSphere)
    (r : ℝ) (hr : 0 < r)
    (hzero : leviCivitaHamiltonian μ c
      (fun i : Fin 4 => r * x i) = 0)
    (hnegative : ∀ t : ℝ, 0 ≤ t → t < r →
      leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0)
    (hfree : ∀ t : ℝ, 0 ≤ t → t ≤ r →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i)) :
    (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c := by sorry

end BirkhoffGlobalSection
