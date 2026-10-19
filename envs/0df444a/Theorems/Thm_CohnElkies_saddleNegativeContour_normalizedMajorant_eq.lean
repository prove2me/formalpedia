-- Prove2me | Theorems.Thm_CohnElkies_saddleNegativeContour_normalizedMajorant_eq
-- name    : CohnElkies.saddleNegativeContour_normalizedMajorant_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/a3b885b9-2c68-463c-b72e-586e6f62eb82
-- title:
--   CohnElkies.saddleNegativeContour_normalizedMajorant_eq
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

theorem CohnElkies.saddleNegativeContour_normalizedMajorant_eq
    {ε : ℝ} (hε : 0 < ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε) /
          saddleOriginValue ε ℓ =
      saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by sorry
