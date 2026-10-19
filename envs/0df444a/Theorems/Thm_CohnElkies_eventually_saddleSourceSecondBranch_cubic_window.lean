-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_cubic_window
-- name    : CohnElkies.eventually_saddleSourceSecondBranch_cubic_window
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/f52864f3-17f1-455c-b0f7-c63df05ce2d1
-- title:
--   CohnElkies.eventually_saddleSourceSecondBranch_cubic_window
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

theorem CohnElkies.eventually_saddleSourceSecondBranch_cubic_window :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            ∀ T : ℝ,
              |T| ≤
                saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
              (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
                  |T| ^ 3 < κ := by sorry
