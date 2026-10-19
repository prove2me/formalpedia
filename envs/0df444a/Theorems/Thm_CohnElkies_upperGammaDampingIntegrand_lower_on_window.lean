-- Prove2me | Theorems.Thm_CohnElkies_upperGammaDampingIntegrand_lower_on_window
-- name    : CohnElkies.upperGammaDampingIntegrand_lower_on_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/9c49e739-e111-4cdb-864b-fdb41608aec9
-- title:
--   CohnElkies.upperGammaDampingIntegrand_lower_on_window
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

theorem CohnElkies.upperGammaDampingIntegrand_lower_on_window
    {ℓ η T a : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (ha : 0 < a)
    (haη : a ≤ η⁻¹)
    (haT : a ≤ |T|⁻¹)
    (hT : T ≠ 0) :
    (ℓ / (8 * Real.exp 1)) * T ^ 2 ≤
      upperGammaDampingIntegrand ℓ η T a := by sorry
