-- Prove2me | Theorems.Thm_CohnElkies_upperPositiveHalfGamma_scaled_sq_le
-- name    : CohnElkies.upperPositiveHalfGamma_scaled_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/fdea973c-1a1e-483e-80bb-691f476863fd
-- title:
--   CohnElkies.upperPositiveHalfGamma_scaled_sq_le
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
open Filter MeasureTheory Set
open scoped Topology BigOperators

theorem CohnElkies.upperPositiveHalfGamma_scaled_sq_le
    (n : ℕ) (x : ℝ) :
    Real.Gamma ((n : ℝ) + 1 / 2) ^ 2 ≤
      ‖Complex.Gamma
        (((((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
          Complex.I * (x : ℂ))‖ ^ 2 *
        Real.cosh (Real.pi * x) := by sorry
