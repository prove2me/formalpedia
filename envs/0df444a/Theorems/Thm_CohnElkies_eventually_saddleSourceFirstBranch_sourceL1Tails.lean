-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSourceFirstBranch_sourceL1Tails
-- name    : CohnElkies.eventually_saddleSourceFirstBranch_sourceL1Tails
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/9ab1e9e6-bf91-463f-a9c5-482a47ef5fb6
-- title:
--   CohnElkies.eventually_saddleSourceFirstBranch_sourceL1Tails
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

theorem CohnElkies.eventually_saddleSourceFirstBranch_sourceL1Tails :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                  ‖saddleSourceCenteredPlusIntegrand ε ℓ u
                      (saddleSourceStationaryLogRadius ε ℓ u) T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * (u : ℂ))‖) ∧
              (1 + ε / 4 ≤ u →
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                      (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    ‖saddleSourceCenteredMinusIntegrand ε ℓ u
                        (saddleSourceStationaryLogRadius ε ℓ u) T‖) <
                  κ * ‖minusPolynomial ε
                    (Complex.I * (u : ℂ))‖) := by sorry
