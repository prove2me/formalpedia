-- Prove2me | Theorems.Thm_CompactnessConjecture_orderedThetaWitness_card
-- name    : CompactnessConjecture.orderedThetaWitness_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/ae98ff32-220f-416e-b89f-286f89dd1ca5
-- title:
--   CompactnessConjecture.orderedThetaWitness_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.orderedThetaWitness_card
    {n : ℕ} (host : SimpleGraph (Fin n)) :
    Fintype.card (OrderedThetaWitness host) =
      orderedThetaTripleCount host := by sorry
