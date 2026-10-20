-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_weighted_tail_explicit
-- name    : CohnElkies.eventually_saddleSource_secondBranch_weighted_tail_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/0a11b74d-4bd2-4483-8a6f-e35fc9bdb3e3
-- title:
--   CohnElkies.eventually_saddleSource_secondBranch_weighted_tail_explicit
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

theorem CohnElkies.eventually_saddleSource_secondBranch_weighted_tail_explicit :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ R : ℝ, 0 ≤ R →
            6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ →
              (∫ T : ℝ in saddleGaussianTailSet R,
                saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceContourDamping
                      ε ℓ (1 + δ) T)) ≤
                2 * Real.exp
                    (-(saddleSourceSecondBranchGaussianRate
                      ε ℓ δ / 4) * R ^ 2) *
                  Real.sqrt
                    (Real.pi /
                      (saddleSourceSecondBranchGaussianRate
                        ε ℓ δ / 4)) +
                Real.exp
                    (-saddleSourceSecondBranchOuterBarrier
                      ε ℓ δ) *
                  (2 * max (1 : ℝ)
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
                            ℓ / 2))) := by sorry
