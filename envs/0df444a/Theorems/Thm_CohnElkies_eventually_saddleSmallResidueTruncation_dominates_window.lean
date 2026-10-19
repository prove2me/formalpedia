-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSmallResidueTruncation_dominates_window
-- name    : CohnElkies.eventually_saddleSmallResidueTruncation_dominates_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/c29ec643-3b73-44bd-a8d5-1f05652d80bc
-- title:
--   CohnElkies.eventually_saddleSmallResidueTruncation_dominates_window
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

theorem CohnElkies.eventually_saddleSmallResidueTruncation_dominates_window
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          2 * y ≤
            (saddleSmallResidueTruncation ℓ : ℝ) + 2 := by sorry
