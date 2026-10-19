-- Prove2me | Theorems.Thm_CompactnessConjecture_choose_three_factorial_identity
-- name    : CompactnessConjecture.choose_three_factorial_identity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/12ecf7e5-8d59-4137-a16c-b48425e1af5f
-- title:
--   CompactnessConjecture.choose_three_factorial_identity
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.choose_three_factorial_identity (t : ℕ) :
    6 * t.choose 3 = t * (t - 1) * (t - 2) := by sorry
