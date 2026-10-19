-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphLine_zero_diagonal_disjoint
-- name    : CompactnessConjecture.symmetricGraphLine_zero_diagonal_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/eb011095-a6ff-4a6c-93c9-8c7dc73b1247
-- title:
--   CompactnessConjecture.symmetricGraphLine_zero_diagonal_disjoint
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symmetricGraphLine_zero_diagonal_disjoint
    {b b' : K} (h : b ≠ b') :
    Disjoint (symmetricGraphLine K 0 b 0).1
      (symmetricGraphLine K 0 b' 0).1 := by sorry
