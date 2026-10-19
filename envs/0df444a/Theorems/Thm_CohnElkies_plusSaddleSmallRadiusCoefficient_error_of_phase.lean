-- Prove2me | Theorems.Thm_CohnElkies_plusSaddleSmallRadiusCoefficient_error_of_phase
-- name    : CohnElkies.plusSaddleSmallRadiusCoefficient_error_of_phase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/c0c8a820-d2e1-47a5-9370-7f71f7064f9a
-- title:
--   CohnElkies.plusSaddleSmallRadiusCoefficient_error_of_phase
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

theorem CohnElkies.plusSaddleSmallRadiusCoefficient_error_of_phase
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ)
    (C : ℝ) (hC : 0 ≤ C)
    (hphase :
      |ℓ *
          (realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ) -
              realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
        C * (n : ℝ) ^ 2 / ℓ) :
    |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
      (C * (n : ℝ) ^ 2 / ℓ +
        (18 / beta ε) * ((n : ℝ) / ℓ)) *
          Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by sorry
