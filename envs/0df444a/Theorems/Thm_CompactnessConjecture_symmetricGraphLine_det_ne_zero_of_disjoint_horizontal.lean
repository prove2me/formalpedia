-- Prove2me | Theorems.Thm_CompactnessConjecture_symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
-- name    : CompactnessConjecture.symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/f2651f7f-dc40-41b4-889b-c3cbb3f9d4da
-- title:
--   CompactnessConjecture.symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
    (a b c : K)
    (hhorizontal :
      Disjoint (symmetricGraphLine K a b c).1
        (symmetricGraphLine K 0 0 0).1) :
    symmetricDet a b c ≠ 0 := by sorry
