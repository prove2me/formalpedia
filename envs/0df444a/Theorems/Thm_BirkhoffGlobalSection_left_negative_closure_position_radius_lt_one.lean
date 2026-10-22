-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_position_radius_lt_one
-- name    : BirkhoffGlobalSection.left_negative_closure_position_radius_lt_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:55:23.001887+00:00
-- url     : https://prove2.me/theorems/688fa0b1-c15c-4fb3-b48a-f119ec95dc9e
-- title:
--   The inner negative-energy closure stays inside a subunit position circle
-- statement:
--   For subcritical energy, there is a squared position radius strictly less than one that bounds the Levi-Civita position image of every point in the closure of the origin negative-energy component. The positive-energy inner Hill circle prevents that connected negative region from reaching the second primary.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region barrier.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_position_radius_lt_one (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ ρ : ℝ, ρ < 1 ∧
      ∀ s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))),
        ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2 ≤ ρ := by sorry

end BirkhoffGlobalSection
