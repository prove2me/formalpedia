-- Prove2me | Theorems.Thm_CompactnessConjecture_encodedJQuotient_no_isolated
-- name    : CompactnessConjecture.encodedJQuotient_no_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:35.440987+00:00
-- url     : https://prove2.me/theorems/1c06ccd5-390b-44b8-b240-81b44ece5173
-- title:
--   CompactnessConjecture.encodedJQuotient_no_isolated
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph

theorem CompactnessConjecture.encodedJQuotient_no_isolated
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph jTemplate f)).graph := by sorry
