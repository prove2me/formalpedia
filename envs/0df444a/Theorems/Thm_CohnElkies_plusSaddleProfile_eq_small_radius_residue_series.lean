-- Prove2me | Theorems.Thm_CohnElkies_plusSaddleProfile_eq_small_radius_residue_series
-- name    : CohnElkies.plusSaddleProfile_eq_small_radius_residue_series
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/f67611bf-9d60-47bd-8fbc-5a6e9b74db64
-- title:
--   CohnElkies.plusSaddleProfile_eq_small_radius_residue_series
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

theorem CohnElkies.plusSaddleProfile_eq_small_radius_residue_series
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r =
      (saddleOriginValue ε ℓ : ℂ) *
        ((∑ n ∈ Finset.range (N + 1),
          (-saddleSmallRadiusVariable ε r) ^ n /
            (n.factorial : ℝ) *
              plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r := by sorry
