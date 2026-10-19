-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricQuadratic_eq_bilinear
-- name    : CompactnessConjecture.symmetricQuadratic_eq_bilinear
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/80d4547e-622e-49bc-9e8d-a2b846da1693
-- title:
--   CompactnessConjecture.symmetricQuadratic_eq_bilinear
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [CommRing K]

theorem CompactnessConjecture.symmetricQuadratic_eq_bilinear
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by sorry
