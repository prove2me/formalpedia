-- Prove2me | Theorems.Thm_CompactnessConjecture_kernelNormalForm_kAdmissible
-- name    : CompactnessConjecture.kernelNormalForm_kAdmissible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/4d821929-fdc7-4957-ad46-33b86dbf2382
-- title:
--   CompactnessConjecture.kernelNormalForm_kAdmissible
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph

theorem CompactnessConjecture.kernelNormalForm_kAdmissible
    {V : Type*} (g : KVertex → V)
    (hcolor : ∀ u v, g u = g v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v : KVertex | v.1 = copy}) :
    KAdmissible (kernelNormalForm g) := by sorry
