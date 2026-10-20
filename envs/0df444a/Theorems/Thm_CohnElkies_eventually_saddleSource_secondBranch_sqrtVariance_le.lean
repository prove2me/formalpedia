-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_sqrtVariance_le
-- name    : CohnElkies.eventually_saddleSource_secondBranch_sqrtVariance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/2e09ffe0-1c18-451e-807f-91574f318dac
-- title:
--   CohnElkies.eventually_saddleSource_secondBranch_sqrtVariance_le
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

theorem CohnElkies.eventually_saddleSource_secondBranch_sqrtVariance_le :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Real.sqrt
              (ℓ * saddleSourceGaussianVariance
                ε ℓ (1 + δ)) ≤
            Real.sqrt
                (saddleSourceSecondBranchVarianceCoefficient ε) *
              Real.sqrt ℓ *
                Real.exp
                  (((shellLocation ε + 1) / 2) * δ) := by sorry
