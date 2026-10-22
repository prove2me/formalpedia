-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regularized_ray_energy_continuous_on_segment
-- name    : BirkhoffGlobalSection.regularized_ray_energy_continuous_on_segment
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:24:49.485646+00:00
-- url     : https://prove2.me/theorems/329020b3-262c-4fa9-9c30-98125b2389b2
-- title:
--   Continuity of regularized energy on a collision-free radial segment
-- statement:
--   Along any finite radial segment of Levi-Civita phase space that remains disjoint from the second collision, the regularized Hamiltonian is a continuous function of the radial parameter. The kinetic and Coriolis terms are polynomial; the only denominator is the square root of the second-collision distance, which stays positive by hypothesis.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, equation (2.2).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem regularized_ray_energy_continuous_on_segment
    (μ c : ℝ) (x : Phase) (R : ℝ)
    (hfree : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i)) :
    ContinuousOn (fun r : ℝ => leviCivitaHamiltonian μ c
      (fun i : Fin 4 => r * x i)) (Set.Icc 0 R) := by sorry

end BirkhoffGlobalSection
