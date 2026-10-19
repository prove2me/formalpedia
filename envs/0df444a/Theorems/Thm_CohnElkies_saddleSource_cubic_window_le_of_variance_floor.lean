-- Prove2me | Theorems.Thm_CohnElkies_saddleSource_cubic_window_le_of_variance_floor
-- name    : CohnElkies.saddleSource_cubic_window_le_of_variance_floor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/55b0242c-90f0-4a62-95ae-9eb826d9e461
-- title:
--   CohnElkies.saddleSource_cubic_window_le_of_variance_floor
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

theorem CohnElkies.saddleSource_cubic_window_le_of_variance_floor
    {ℓ V M C V₀ z T : ℝ}
    (hℓ : 0 < ℓ) (hV₀ : 0 < V₀)
    (hfloor : V₀ ≤ V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 /
        (Real.sqrt ℓ * Real.sqrt V₀) := by sorry
