-- Prove2me | Theorems.Thm_ConnesRigidity_FiniteCarry_carry_add_right
-- name    : ConnesRigidity.FiniteCarry.carry_add_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/702db8a3-4dc2-4bb7-a8df-f42332fb9a05
-- title:
--   ConnesRigidity.FiniteCarry.carry_add_right
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | ConnesRigidity | external Lean 4.33.1 validation; bundle SHA256 4ed9232ec35753a258ad689b720fbf6aae9317c7cf506b5797de1710cec6f4a3

import Mathlib
import Definitions.Def_ConnesRigidity
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
open ConnesRigidity.FiniteCarry

theorem ConnesRigidity.FiniteCarry.carry_add_right (x y z : Bit) :
    carry x (y + z) = carry x y + carry x z := by sorry
