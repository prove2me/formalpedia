-- Prove2me | Theorems.Thm_CompactnessConjecture_member_eventual_lower_of_prime_power_avoidance
-- name    : CompactnessConjecture.member_eventual_lower_of_prime_power_avoidance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/579d8d4c-23e1-44dd-a9ef-ae4ba969dd3b
-- title:
--   CompactnessConjecture.member_eventual_lower_of_prime_power_avoidance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology

theorem CompactnessConjecture.member_eventual_lower_of_prime_power_avoidance
    {forbidden : FiniteGraph}
    (hmember : forbidden ∈ proposedFamily)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.graph.Free
        (symplecticQuadrangle (GaloisField t j))) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ) := by sorry
