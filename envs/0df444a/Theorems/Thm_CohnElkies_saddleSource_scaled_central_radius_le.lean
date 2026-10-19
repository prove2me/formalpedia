-- Prove2me | Theorems.Thm_CohnElkies_saddleSource_scaled_central_radius_le
-- name    : CohnElkies.saddleSource_scaled_central_radius_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/ca5f2998-9fc4-47d4-bb84-668806adc404
-- title:
--   CohnElkies.saddleSource_scaled_central_radius_le
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
open Filter Set MeasureTheory intervalIntegral
open scoped Topology

theorem CohnElkies.saddleSource_scaled_central_radius_le
    {ℓ η V c U z : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c) (hηU : η ≤ U)
    (hz : 0 ≤ z) (hvariance : c ≤ η * V) :
    z / Real.sqrt (ℓ * V) ≤
      (U / Real.sqrt c) *
        (z / Real.sqrt (ℓ * η)) := by sorry
