-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_radial_nonpositive
-- name    : BirkhoffGlobalSection.left_negative_closure_radial_nonpositive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:07:27.570397+00:00
-- url     : https://prove2.me/theorems/d85a56c6-eefe-4082-b935-0c167645cb30
-- title:
--   Every radial contraction of the inner negative closure has nonpositive energy
-- statement:
--   For subcritical energy, each contraction toward the origin of a point in the negative-component closure has nonpositive regularized Hamiltonian. This is the weak radial star-shaped property of the inner sublevel region.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, star-shaped regularized component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_radial_nonpositive (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      ∀ a : ℝ, 0 ≤ a → a < 1 →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => a * s i) ≤ 0 := by sorry

end BirkhoffGlobalSection
