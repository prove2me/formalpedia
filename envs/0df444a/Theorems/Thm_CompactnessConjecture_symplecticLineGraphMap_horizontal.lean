-- Prove2me | Theorems.Thm_CompactnessConjecture_symplecticLineGraphMap_horizontal
-- name    : CompactnessConjecture.symplecticLineGraphMap_horizontal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/b8292710-ef0c-4c32-b1b6-d6b901713d9f
-- title:
--   CompactnessConjecture.symplecticLineGraphMap_horizontal
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symplecticLineGraphMap_horizontal
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by sorry
