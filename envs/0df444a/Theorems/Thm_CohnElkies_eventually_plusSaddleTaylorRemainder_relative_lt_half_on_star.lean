-- Prove2me | Theorems.Thm_CohnElkies_eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
-- name    : CohnElkies.eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/4c42a65a-8d92-4f5d-8b03-7a1053a201f4
-- title:
--   CohnElkies.eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
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

theorem CohnElkies.eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
    {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ, 0 < r → r ≤ saddleSmallRadiusStar ε d →
        let ℓ : ℝ := (d : ℝ) / 2
        let N : ℕ := saddleSmallResidueTruncation ℓ
        let y : ℝ := saddleSmallRadiusVariable ε r
        Real.exp y *
          ‖plusSaddleTaylorRemainder ε ℓ N r /
            (saddleOriginValue ε ℓ : ℂ)‖ < 1 / 2 := by sorry
