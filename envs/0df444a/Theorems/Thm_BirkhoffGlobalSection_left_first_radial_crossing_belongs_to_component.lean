-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_first_radial_crossing_belongs_to_component
-- name    : BirkhoffGlobalSection.left_first_radial_crossing_belongs_to_component
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:11:12.630985+00:00
-- url     : https://prove2.me/theorems/36723953-465e-4384-a29e-8f5f6ea9baf2
-- title:
--   First radial zero belongs to the left component
-- statement:
--   Suppose a unit ray has positive regularized energy at radius $R>0$ and avoids the second collision along its entire initial segment. Since the energy at the origin is negative, continuity gives a first zero at a positive radius below $R$. This lemma identifies that first zero with the connected energy component containing the left-primary collision state.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, radial description of the subcritical Hill component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_first_radial_crossing_belongs_to_component (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (x : Phase) (hx : x ∈ unitThreeSphere)
    (R : ℝ) (hR : 0 < R)
    (hpositive : 0 < leviCivitaHamiltonian μ c
      (fun i : Fin 4 => R * x i))
    (hfree : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i)) :
    ∃ r : ℝ, 0 < r ∧
      (fun i : Fin 4 => r * x i) ∈ leftEnergyComponent μ c := by sorry

end BirkhoffGlobalSection
