-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceSecondBranch_outerMoment_le
-- name    : CohnElkies.saddleSourceSecondBranch_outerMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/9bea2483-f54b-402d-a4a7-1d0bb82e0f54
-- title:
--   CohnElkies.saddleSourceSecondBranch_outerMoment_le
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

theorem CohnElkies.saddleSourceSecondBranch_outerMoment_le
    {ℓ δ : ℝ} (hℓ : 1 ≤ ℓ) (hδ : 0 ≤ δ) :
    2 * max (1 : ℝ)
        ((Real.sqrt
          (saddleSourceSecondBranchGammaGaussianRate
            ℓ δ / 6) ^ 3)⁻¹) *
          Real.sqrt
            (Real.pi /
              (saddleSourceSecondBranchGammaGaussianRate
                ℓ δ / 2)) +
      2 * max (1 : ℝ)
        (((saddleSourceSecondBranchGammaLinearRate
          ℓ / 6) ^ 3)⁻¹) *
          (2 /
            (saddleSourceSecondBranchGammaLinearRate
              ℓ / 2)) ≤
        saddleSourceSecondBranchMomentCoefficient *
          (2 + δ) ^ 4 := by sorry
