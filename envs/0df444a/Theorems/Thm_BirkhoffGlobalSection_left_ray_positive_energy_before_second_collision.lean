-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_ray_positive_energy_before_second_collision
-- name    : BirkhoffGlobalSection.left_ray_positive_energy_before_second_collision
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:11:13.310979+00:00
-- url     : https://prove2.me/theorems/d826c8d0-11f8-4501-a511-034f32557882
-- title:
--   A positive-energy point on every ray before second collision
-- statement:
--   For every unit phase direction $x\in S^3$, a ray leaving the origin reaches a positive value of the regularized Hamiltonian at some radius $R>0$, while the entire radial segment from $0$ to $R$ remains away from the second collision. The subcritical Hill-circle barrier supplies such a radius for directions with nonzero position coordinate; purely momentum directions follow from the quadratic kinetic term.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, radial description of the subcritical Hill component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_ray_positive_energy_before_second_collision (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere,
      ∃ R : ℝ, 0 < R ∧
        leviCivitaHamiltonian μ c (fun i : Fin 4 => R * x i) > 0 ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ R →
          0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i) := by sorry

end BirkhoffGlobalSection
