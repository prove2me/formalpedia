-- Prove2me | Theorems.Thm_CompactnessConjecture_four_path_common_second_neighbor_sum_lower
-- name    : CompactnessConjecture.four_path_common_second_neighbor_sum_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/8b52292b-179d-4d65-a0ba-92dd9f8d2def
-- title:
--   CompactnessConjecture.four_path_common_second_neighbor_sum_lower
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.four_path_common_second_neighbor_sum_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by sorry
