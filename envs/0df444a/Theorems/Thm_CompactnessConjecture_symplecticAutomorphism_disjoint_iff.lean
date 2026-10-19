-- Prove2me | Theorems.Thm_CompactnessConjecture_symplecticAutomorphism_disjoint_iff
-- name    : CompactnessConjecture.symplecticAutomorphism_disjoint_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/96c3b582-c63a-4eee-992f-992e3f27f979
-- title:
--   CompactnessConjecture.symplecticAutomorphism_disjoint_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem CompactnessConjecture.symplecticAutomorphism_disjoint_iff
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K) :
    Disjoint (symplecticAutomorphismLine K e L).1
        (symplecticAutomorphismLine K e M).1 ↔
      Disjoint L.1 M.1 := by sorry
