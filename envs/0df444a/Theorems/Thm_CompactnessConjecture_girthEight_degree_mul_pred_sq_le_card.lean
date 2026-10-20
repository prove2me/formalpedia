-- Prove2me | Theorems.Thm_CompactnessConjecture_girthEight_degree_mul_pred_sq_le_card
-- name    : CompactnessConjecture.girthEight_degree_mul_pred_sq_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/bb52e3ed-1e0c-41af-b236-87f59f2dbd96
-- title:
--   CompactnessConjecture.girthEight_degree_mul_pred_sq_le_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.girthEight_degree_mul_pred_sq_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v)
    (u : V) :
    G.degree u * (d - 1) ^ 2 ≤ Fintype.card V := by sorry
