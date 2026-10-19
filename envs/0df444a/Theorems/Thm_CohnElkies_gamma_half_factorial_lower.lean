-- Prove2me | Theorems.Thm_CohnElkies_gamma_half_factorial_lower
-- name    : CohnElkies.gamma_half_factorial_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/bd3bceab-9325-47df-9798-0d0480cc624d
-- title:
--   CohnElkies.gamma_half_factorial_lower
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
open Filter Set MeasureTheory
open scoped Topology BigOperators

theorem CohnElkies.gamma_half_factorial_lower (N : ℕ) :
    Real.Gamma (3 / 2 : ℝ) * (N.factorial : ℝ) ≤
      Real.Gamma ((N : ℝ) + 3 / 2) := by sorry
