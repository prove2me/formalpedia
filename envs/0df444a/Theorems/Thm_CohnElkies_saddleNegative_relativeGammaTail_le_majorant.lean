-- Prove2me | Theorems.Thm_CohnElkies_saddleNegative_relativeGammaTail_le_majorant
-- name    : CohnElkies.saddleNegative_relativeGammaTail_le_majorant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/65b3d3ce-72c9-4727-8c2a-d0261c6c12c0
-- title:
--   CohnElkies.saddleNegative_relativeGammaTail_le_majorant
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
open Filter Set MeasureTheory
open scoped Topology BigOperators

theorem CohnElkies.saddleNegative_relativeGammaTail_le_majorant
    {C K Kε ℓ y : ℝ}
    (hKε : 0 ≤ Kε)
    (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
      (Kε * Real.sqrt y *
          y ^ saddleSmallResidueTruncation ℓ /
            Real.Gamma
              ((saddleSmallResidueTruncation ℓ : ℝ) + 3 / 2) *
        Real.exp
          (K *
            (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
              ℓ)) ≤
      saddleNegativeRelativeGammaTailMajorant C K Kε ℓ := by sorry
