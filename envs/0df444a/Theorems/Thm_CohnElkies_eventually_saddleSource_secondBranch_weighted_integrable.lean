-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_weighted_integrable
-- name    : CohnElkies.eventually_saddleSource_secondBranch_weighted_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/de73063d-88b2-4b78-a983-a631733818ee
-- title:
--   CohnElkies.eventually_saddleSource_secondBranch_weighted_integrable
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

theorem CohnElkies.eventually_saddleSource_secondBranch_weighted_integrable :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Integrable
            (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T)) := by sorry
