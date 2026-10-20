-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_normalized_tail_bound
-- name    : CohnElkies.eventually_saddleSource_secondBranch_normalized_tail_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/22139a2a-3412-430b-a8fd-7be8c5c8dcce
-- title:
--   CohnElkies.eventually_saddleSource_secondBranch_normalized_tail_bound
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

theorem CohnElkies.eventually_saddleSource_secondBranch_normalized_tail_bound :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ z : ℝ, 0 ≤ z →
            6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance
                    ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (z / Real.sqrt
                      (ℓ * saddleSourceGaussianVariance
                        ε ℓ (1 + δ))),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping
                        ε ℓ (1 + δ) T)) ≤
                2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
                  Real.exp
                    (-(z ^ 2 / (400 * Real.exp 1))) +
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance
                      ε ℓ (1 + δ)) *
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
