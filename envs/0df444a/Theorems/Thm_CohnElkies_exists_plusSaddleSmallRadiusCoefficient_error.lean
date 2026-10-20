-- Prove2me | Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadiusCoefficient_error
-- name    : CohnElkies.exists_plusSaddleSmallRadiusCoefficient_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/109b2c4d-38f3-4345-9b0b-f7ae7c7a5525
-- title:
--   CohnElkies.exists_plusSaddleSmallRadiusCoefficient_error
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
open scoped Topology

theorem CohnElkies.exists_plusSaddleSmallRadiusCoefficient_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
            (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
              Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by sorry
