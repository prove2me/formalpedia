-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphLine_coordinateCenter_intersection_iff
-- name    : CompactnessConjecture.symmetricGraphLine_coordinateCenter_intersection_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/a3aa7c7d-8f30-47bc-af2f-f3ef8e0c1304
-- title:
--   CompactnessConjecture.symmetricGraphLine_coordinateCenter_intersection_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symmetricGraphLine_coordinateCenter_intersection_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ w : SymplecticVector K,
      w ≠ 0 ∧ w ∈ (symmetricGraphLine K a b c).1 ∧
        w ∈ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by sorry
