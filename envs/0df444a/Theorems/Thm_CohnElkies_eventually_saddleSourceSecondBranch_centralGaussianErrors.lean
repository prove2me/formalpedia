-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_centralGaussianErrors
-- name    : CohnElkies.eventually_saddleSourceSecondBranch_centralGaussianErrors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/3837d31d-6438-4121-9438-4422e4d2491f
-- title:
--   CohnElkies.eventually_saddleSourceSecondBranch_centralGaussianErrors
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

theorem CohnElkies.eventually_saddleSourceSecondBranch_centralGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (‖∫ T : ℝ in
              Icc (-(saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)))
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                (saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                  (saddleSourceStationaryLogRadius ε ℓ (1 + δ)) T -
                    saddleSourceGaussianPlusIntegrand
                      ε ℓ (1 + δ) T)‖ <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
            (‖∫ T : ℝ in
              Icc (-(saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)))
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                (saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                  (saddleSourceStationaryLogRadius ε ℓ (1 + δ)) T -
                    saddleSourceGaussianMinusIntegrand
                      ε ℓ (1 + δ) T)‖ <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ (1 + δ) T)) := by sorry
