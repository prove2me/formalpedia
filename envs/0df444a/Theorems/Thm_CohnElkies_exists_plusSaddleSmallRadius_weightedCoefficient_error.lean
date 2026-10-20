-- Prove2me | Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadius_weightedCoefficient_error
-- name    : CohnElkies.exists_plusSaddleSmallRadius_weightedCoefficient_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/1826c2dc-f33e-4581-a4cb-dbb3dca66baf
-- title:
--   CohnElkies.exists_plusSaddleSmallRadius_weightedCoefficient_error
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
open Filter MeasureTheory Set
open scoped Topology

theorem CohnElkies.exists_plusSaddleSmallRadius_weightedCoefficient_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ →
          ∀ y : ℝ, 0 ≤ y →
            (∑ n ∈ Finset.range (N + 1),
              (y ^ n / (n.factorial : ℝ)) *
                |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) ≤
              (C / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                  (2 * y + y ^ 2) * Real.exp y := by sorry
