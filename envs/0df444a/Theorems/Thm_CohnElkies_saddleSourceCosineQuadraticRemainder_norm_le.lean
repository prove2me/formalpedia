-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceCosineQuadraticRemainder_norm_le
-- name    : CohnElkies.saddleSourceCosineQuadraticRemainder_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/a43099e5-247c-4926-a00e-748f0ffb6831
-- title:
--   CohnElkies.saddleSourceCosineQuadraticRemainder_norm_le
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

theorem CohnElkies.saddleSourceCosineQuadraticRemainder_norm_le
    (a u T : ℝ) :
    ‖saddleSourceCosineQuadraticRemainder a u T‖ ≤
      Real.cosh (u * a) * |a * T| ^ 3 / 6 := by sorry
