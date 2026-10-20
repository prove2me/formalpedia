-- Prove2me | Theorems.Thm_CohnElkies_plusSaddleProfile_re_pos_of_relative_residue_bounds
-- name    : CohnElkies.plusSaddleProfile_re_pos_of_relative_residue_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/a6ace0d8-10b6-466b-8e9b-7ad9d6dfe9c8
-- title:
--   CohnElkies.plusSaddleProfile_re_pos_of_relative_residue_bounds
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

theorem CohnElkies.plusSaddleProfile_re_pos_of_relative_residue_bounds
    {ε ℓ r : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    (N : ℕ)
    (hfinite :
      Real.exp (saddleSmallRadiusVariable ε r) *
        |(∑ n ∈ Finset.range (N + 1),
            (-saddleSmallRadiusVariable ε r) ^ n /
              (n.factorial : ℝ) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-(saddleSmallRadiusVariable ε r))| <
        (1 / 2 : ℝ))
    (hremainder :
      Real.exp (saddleSmallRadiusVariable ε r) *
        ‖plusSaddleTaylorRemainder ε ℓ N r /
          (saddleOriginValue ε ℓ : ℂ)‖ <
        (1 / 2 : ℝ)) :
    0 < (plusSaddleProfile ε ℓ r).re := by sorry
