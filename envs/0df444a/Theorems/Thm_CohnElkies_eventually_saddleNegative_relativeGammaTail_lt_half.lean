-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleNegative_relativeGammaTail_lt_half
-- name    : CohnElkies.eventually_saddleNegative_relativeGammaTail_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/e7e4ba27-4636-4f1d-a3da-3bd40e700c28
-- title:
--   CohnElkies.eventually_saddleNegative_relativeGammaTail_lt_half
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

theorem CohnElkies.eventually_saddleNegative_relativeGammaTail_lt_half
    {ε : ℝ} (hε : 0 < ε)
    (C K Kε : ℝ)
    (hC : 0 ≤ C)
    (hK : 0 ≤ K)
    (hKε : 0 ≤ Kε) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          Real.exp y *
            (Kε * Real.sqrt y *
              y ^ saddleSmallResidueTruncation ℓ /
                Real.Gamma
                  ((saddleSmallResidueTruncation ℓ : ℝ) + 3 / 2) *
              Real.exp
                (K *
                  (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
                    ℓ)) < 1 / 2 := by sorry
