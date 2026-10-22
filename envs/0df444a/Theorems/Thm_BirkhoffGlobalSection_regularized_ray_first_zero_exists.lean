-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regularized_ray_first_zero_exists
-- name    : BirkhoffGlobalSection.regularized_ray_first_zero_exists
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:22:20.662725+00:00
-- url     : https://prove2.me/theorems/f4c52d68-746c-4c6a-a78c-cf8df1feeddb
-- title:
--   Existence of the first radial zero of regularized energy
-- statement:
--   The regularized energy starts negative at the origin for $0<\mu<1$ and is positive at radius $R$. If the radial segment avoids the second collision, the energy varies continuously along it; hence it has a first zero $r\in(0,R)$, with strictly negative energy at all earlier radii. This lemma isolates the one-dimensional intermediate-value and first-hit argument.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and equation (2.2), radial energy and Hill-region component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem regularized_ray_first_zero_exists (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (x : Phase) (R : ℝ) (hR : 0 < R)
    (hpositive : 0 < leviCivitaHamiltonian μ c
      (fun i : Fin 4 => R * x i))
    (hfree : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      leviCivitaHamiltonian μ c (fun i : Fin 4 => r * x i) = 0 ∧
      ∀ t : ℝ, 0 ≤ t → t < r →
        leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0 := by sorry

end BirkhoffGlobalSection
