-- Prove2me | Theorems.Thm_CohnElkies_upperGammaDamping_lower_bound
-- name    : CohnElkies.upperGammaDamping_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/12647fc3-4dc5-4c4d-b13a-3c27a1d35842
-- title:
--   CohnElkies.upperGammaDamping_lower_bound
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

theorem CohnElkies.upperGammaDamping_lower_bound
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    (ℓ / (8 * Real.exp 1)) *
        min (T ^ 2 / η) |T| ≤
      upperGammaDamping ℓ η T := by sorry
