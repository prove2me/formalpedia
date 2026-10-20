-- Prove2me | Theorems.Thm_CohnElkies_saddleTaylorContour_rpow
-- name    : CohnElkies.saddleTaylorContour_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/afd80918-f54e-46b5-ac58-cb04b7bf8e2c
-- title:
--   CohnElkies.saddleTaylorContour_rpow
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
open scoped Interval Topology

theorem CohnElkies.saddleTaylorContour_rpow
    (r : ℝ) (N : ℕ) :
    r ^ (-(saddleTaylorContour N)) =
      r ^ (2 * N + 1) := by sorry
