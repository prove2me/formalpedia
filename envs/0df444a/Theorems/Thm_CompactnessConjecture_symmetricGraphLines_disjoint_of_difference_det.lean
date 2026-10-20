-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphLines_disjoint_of_difference_det
-- name    : CompactnessConjecture.symmetricGraphLines_disjoint_of_difference_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/60a932c8-ade5-4d30-8346-ef3b294f84c7
-- title:
--   CompactnessConjecture.symmetricGraphLines_disjoint_of_difference_det
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symmetricGraphLines_disjoint_of_difference_det
    {a b c a' b' c' : K}
    (hdet : symmetricDet (a - a') (b - b') (c - c') ≠ 0) :
    Disjoint (symmetricGraphLine K a b c).1
      (symmetricGraphLine K a' b' c').1 := by sorry
