-- Prove2me | Theorems.Thm_CompactnessConjecture_encodedKQuotient_no_isolated
-- name    : CompactnessConjecture.encodedKQuotient_no_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:35.440987+00:00
-- url     : https://prove2.me/theorems/18e56d98-282c-4656-91e3-00f520d90113
-- title:
--   CompactnessConjecture.encodedKQuotient_no_isolated
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph

theorem CompactnessConjecture.encodedKQuotient_no_isolated
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph kTemplate f)).graph := by sorry
