-- Prove2me | Theorems.Thm_CohnElkies_tendsto_saddleNegativeLogWindowTailMajorant
-- name    : CohnElkies.tendsto_saddleNegativeLogWindowTailMajorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/5583f262-7a75-4088-887f-5e5960d7a2ab
-- title:
--   CohnElkies.tendsto_saddleNegativeLogWindowTailMajorant
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
open Filter Set MeasureTheory
open scoped Topology BigOperators

theorem CohnElkies.tendsto_saddleNegativeLogWindowTailMajorant
    (C : ℝ) :
    Tendsto
      (fun ℓ : ℝ =>
        (1 + (Real.log ℓ / 8 + C)) *
          saddleSmallResidueTailMajorant C ℓ)
      atTop (𝓝 0) := by sorry
