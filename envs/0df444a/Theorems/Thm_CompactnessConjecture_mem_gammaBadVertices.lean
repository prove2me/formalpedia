-- Prove2me | Theorems.Thm_CompactnessConjecture_mem_gammaBadVertices
-- name    : CompactnessConjecture.mem_gammaBadVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/8976bc88-bb8b-4384-87b8-fb26a5fe977f
-- title:
--   CompactnessConjecture.mem_gammaBadVertices
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]

theorem CompactnessConjecture.mem_gammaBadVertices (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by sorry
