-- Prove2me | Theorems.Thm_CompactnessConjecture_jTheta_quotient_injective
-- name    : CompactnessConjecture.jTheta_quotient_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:35.440987+00:00
-- url     : https://prove2.me/theorems/26c684dd-999b-477c-80ff-54361fafc150
-- title:
--   CompactnessConjecture.jTheta_quotient_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.jTheta_quotient_injective
    {f : JVertex → JVertex} (hf : JAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 2 =>
      f (jThetaVertex copy v)) := by sorry
