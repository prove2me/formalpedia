-- Prove2me | Theorems.Thm_CohnElkies_saddleSmallRadiusPhase_pole_factorization
-- name    : CohnElkies.saddleSmallRadiusPhase_pole_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/704bd07f-e21d-4850-a249-4decbb60f60d
-- title:
--   CohnElkies.saddleSmallRadiusPhase_pole_factorization
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

theorem CohnElkies.saddleSmallRadiusPhase_pole_factorization
    (ε ℓ : ℝ) (n : ℕ) :
    Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ)) =
      Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
        Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
        Real.exp
          (ℓ *
            (realHyperbolicShellPhase ε
              (1 + 2 * (n : ℝ) / ℓ) -
                realHyperbolicShellPhase ε 1) -
            2 * (n : ℝ) * saddleShellDerivativeOne ε) := by sorry
