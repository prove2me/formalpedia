-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceSecondBranch_normalizedGaussian_exponent
-- name    : CohnElkies.saddleSourceSecondBranch_normalizedGaussian_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/daf29ad7-6b29-4692-b3a1-80d36a47c554
-- title:
--   CohnElkies.saddleSourceSecondBranch_normalizedGaussian_exponent
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

theorem CohnElkies.saddleSourceSecondBranch_normalizedGaussian_exponent
    {ε ℓ δ z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ (1 + δ)) :
    (saddleSourceSecondBranchGaussianRate ε ℓ δ / 4) *
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))) ^ 2 =
      z ^ 2 / (400 * Real.exp 1) := by sorry
