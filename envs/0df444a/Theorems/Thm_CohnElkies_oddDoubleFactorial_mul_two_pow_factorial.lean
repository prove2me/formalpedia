-- Prove2me | Theorems.Thm_CohnElkies_oddDoubleFactorial_mul_two_pow_factorial
-- name    : CohnElkies.oddDoubleFactorial_mul_two_pow_factorial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/eb52a4dc-0a9a-49c2-bf32-f02e5f81e141
-- title:
--   CohnElkies.oddDoubleFactorial_mul_two_pow_factorial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology

theorem CohnElkies.oddDoubleFactorial_mul_two_pow_factorial (k : ℕ) :
    ((2 * k + 1)‼ : ℝ) * (2 : ℝ) ^ k * (k.factorial : ℝ) =
      ((2 * k + 1).factorial : ℝ) := by sorry
