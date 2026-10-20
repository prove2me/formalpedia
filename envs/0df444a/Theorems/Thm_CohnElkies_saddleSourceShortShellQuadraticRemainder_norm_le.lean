-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceShortShellQuadraticRemainder_norm_le
-- name    : CohnElkies.saddleSourceShortShellQuadraticRemainder_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/584b66b7-1235-4a3d-89aa-07183293992a
-- title:
--   CohnElkies.saddleSourceShortShellQuadraticRemainder_norm_le
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

theorem CohnElkies.saddleSourceShortShellQuadraticRemainder_norm_le
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (u T : ℝ) :
    ‖∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        upperShortShellThirdMoment ε (u - 1) := by sorry
