-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphVector_mem_center_span_iff
-- name    : CompactnessConjecture.symmetricGraphVector_mem_center_span_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/a022f1e1-c997-4e8b-b530-e04b9e4eec0e
-- title:
--   CompactnessConjecture.symmetricGraphVector_mem_center_span_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symmetricGraphVector_mem_center_span_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ s t : K,
      symmetricGraphVector K a b c x y =
        s • symplecticHorizontalVector K x y +
          t • symplecticAnnihilatorVector K x y) ↔
      symmetricQuadratic a b c x y = 0 := by sorry
