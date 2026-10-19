-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricQuadraticEvaluationMatrix_det
-- name    : CompactnessConjecture.symmetricQuadraticEvaluationMatrix_det
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/fd4467bf-bcf8-46f9-a091-c569fd84f6d8
-- title:
--   CompactnessConjecture.symmetricQuadraticEvaluationMatrix_det
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K]

theorem CompactnessConjecture.symmetricQuadraticEvaluationMatrix_det
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) :
    (symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂).det =
      (2 : K) * (x₀ * y₁ - x₁ * y₀) *
        (x₀ * y₂ - x₂ * y₀) * (x₁ * y₂ - x₂ * y₁) := by sorry
