-- Prove2me | Theorems.Thm_CompactnessConjecture_proposedFamily_familyExtremal_isBigO
-- name    : CompactnessConjecture.proposedFamily_familyExtremal_isBigO
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:39.087222+00:00
-- url     : https://prove2.me/theorems/b26c7a0c-7d05-4786-bf2a-222794fdb7b2
-- title:
--   CompactnessConjecture.proposedFamily_familyExtremal_isBigO
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.proposedFamily_familyExtremal_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (familyExtremal proposedFamily n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((21 : ℝ) / 16)) := by sorry
