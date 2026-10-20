-- Prove2me | Theorems.Thm_CompactnessConjecture_encodedKQuotient_isBipartite
-- name    : CompactnessConjecture.encodedKQuotient_isBipartite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:39.087222+00:00
-- url     : https://prove2.me/theorems/366bfd2c-4925-497d-a9b9-7fa6ca6660fb
-- title:
--   CompactnessConjecture.encodedKQuotient_isBipartite
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.encodedKQuotient_isBipartite
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsBipartite := by sorry
