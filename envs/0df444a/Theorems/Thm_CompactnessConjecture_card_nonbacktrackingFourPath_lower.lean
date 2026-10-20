-- Prove2me | Theorems.Thm_CompactnessConjecture_card_nonbacktrackingFourPath_lower
-- name    : CompactnessConjecture.card_nonbacktrackingFourPath_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/4a77df2e-e072-4988-a91d-4cf56bf5819e
-- title:
--   CompactnessConjecture.card_nonbacktrackingFourPath_lower
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.card_nonbacktrackingFourPath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (NonbacktrackingFourPath G u) := by sorry
