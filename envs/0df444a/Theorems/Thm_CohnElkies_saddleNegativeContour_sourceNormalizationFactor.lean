-- Prove2me | Theorems.Thm_CohnElkies_saddleNegativeContour_sourceNormalizationFactor
-- name    : CohnElkies.saddleNegativeContour_sourceNormalizationFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/0f8af80e-d5c5-4b43-959d-445b318f88d2
-- title:
--   CohnElkies.saddleNegativeContour_sourceNormalizationFactor
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

theorem CohnElkies.saddleNegativeContour_sourceNormalizationFactor
    (ε ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ (2 * N + 1) *
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) *
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) /
      (Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by sorry
