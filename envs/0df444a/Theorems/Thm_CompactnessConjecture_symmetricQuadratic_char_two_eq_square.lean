-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricQuadratic_char_two_eq_square
-- name    : CompactnessConjecture.symmetricQuadratic_char_two_eq_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/3c419fd5-0725-4296-b7de-56c9f04a855a
-- title:
--   CompactnessConjecture.symmetricQuadratic_char_two_eq_square
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K] [CharP K 2]

theorem CompactnessConjecture.symmetricQuadratic_char_two_eq_square
    (r s b x y : K) :
    symmetricQuadratic (r ^ 2) b (s ^ 2) x y =
      (r * x + s * y) ^ 2 := by sorry
