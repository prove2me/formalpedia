-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_nonvertical_ray_reaches_inner_circle
-- name    : BirkhoffGlobalSection.nonvertical_ray_reaches_inner_circle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:18:26.883985+00:00
-- url     : https://prove2.me/theorems/873f940a-4c63-447a-915d-6fd9e023b546
-- title:
--   A nonvertical phase ray reaches the inner circle before right collision
-- statement:
--   For any radius $0<r<1$ and any phase ray whose Levi-Civita position coordinate is nonzero, there is a positive ray parameter $R$ at which the physical position reaches the circle of radius $r$ about the left primary. The entire segment from the origin to $R$ stays away from the right collision, because its physical distance from the left primary remains less than one. This algebraic scaling fact is independent of the mass ratio.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, equation (2.2), Levi-Civita position map q+μ=2z².

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem nonvertical_ray_reaches_inner_circle
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (x : Phase) (hx : 0 < zNormSq x) :
    ∃ R : ℝ, 0 < R ∧
      ((leviCivitaPosition 0 (fun i : Fin 4 => R * x i)) 0) ^ 2 +
        ((leviCivitaPosition 0 (fun i : Fin 4 => R * x i)) 1) ^ 2 = r ^ 2 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ R →
        0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i) := by sorry

end BirkhoffGlobalSection
