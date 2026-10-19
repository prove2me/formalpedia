-- Prove2me | Theorems.Thm_CompactnessConjecture_kQuotients_mem_iff
-- name    : CompactnessConjecture.kQuotients_mem_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:34.487131+00:00
-- url     : https://prove2.me/theorems/ae1c5509-f3c5-4621-8b8d-6d8b21b60fe9
-- title:
--   CompactnessConjecture.kQuotients_mem_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.kQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ kQuotients ↔
      ∃ f : KVertex → KVertex, KAdmissible f ∧
        encodeFiniteGraph (quotientGraph kTemplate f) = graph := by sorry
