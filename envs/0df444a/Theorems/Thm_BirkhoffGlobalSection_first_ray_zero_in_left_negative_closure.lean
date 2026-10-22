-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_first_ray_zero_in_left_negative_closure
-- name    : BirkhoffGlobalSection.first_ray_zero_in_left_negative_closure
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T12:28:45.58815+00:00
-- url     : https://prove2.me/theorems/28523cfb-0be1-4f89-b058-905083d3bce5
-- title:
--   A first ray zero approaches the origin negative-energy region
-- statement:
--   A ray segment from the origin has negative regularized energy and avoids the second collision until its endpoint at radius $r$. Its interior is therefore contained in the connected negative-energy region based at the origin. The endpoint belongs to the closure of that region. This statement isolates the elementary path and closure argument.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region description.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem first_ray_zero_in_left_negative_closure (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (x : Phase) (r : ℝ) (hr : 0 < r)
    (hnegative : ∀ t : ℝ, 0 ≤ t → t < r →
      leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0)
    (hfree : ∀ t : ℝ, 0 ≤ t → t ≤ r →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i)) :
    (fun i : Fin 4 => r * x i) ∈ closure
      (connectedComponentIn
        {s : Phase | leviCivitaHamiltonian μ c s < 0 ∧
          0 < secondCollisionDistanceSq s}
        (fun _ : Fin 4 => (0 : ℝ))) := by sorry

end BirkhoffGlobalSection
