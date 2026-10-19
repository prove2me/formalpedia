-- Prove2me | Theorems.Thm_CompactnessConjecture_square_surjective_char_two
-- name    : CompactnessConjecture.square_surjective_char_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/94c35d01-d8a0-4d6f-83c1-68c23e1af765
-- title:
--   CompactnessConjecture.square_surjective_char_two
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K] [CharP K 2]

theorem CompactnessConjecture.square_surjective_char_two [Finite K] :
    Function.Surjective (fun x : K => x ^ 2) := by sorry
