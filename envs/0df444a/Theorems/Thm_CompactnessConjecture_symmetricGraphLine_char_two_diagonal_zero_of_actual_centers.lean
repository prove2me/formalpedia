-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
-- name    : CompactnessConjecture.symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/95327b87-3fdf-44f3-84ae-985c51e7328d
-- title:
--   CompactnessConjecture.symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
variable [CharP K 2] [Finite K]

theorem CompactnessConjecture.symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
    {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x y
            (projectiveDirection_nonzero_left K hind)).1)
    (hsecond : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x' y'
            (projectiveDirection_nonzero_right K hind)).1) :
    a = 0 ∧ c = 0 := by sorry
