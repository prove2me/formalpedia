-- Prove2me | Theorems.Thm_CohnElkies_plusSaddleTaylorRemainder_negativeContour_relative_bound
-- name    : CohnElkies.plusSaddleTaylorRemainder_negativeContour_relative_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/b142b913-2b9c-4028-bfe3-02102bb3f792
-- title:
--   CohnElkies.plusSaddleTaylorRemainder_negativeContour_relative_bound
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
open scoped Topology BigOperators

theorem CohnElkies.plusSaddleTaylorRemainder_negativeContour_relative_bound
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r /
      (saddleOriginValue ε ℓ : ℂ)‖ ≤
      saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by sorry
