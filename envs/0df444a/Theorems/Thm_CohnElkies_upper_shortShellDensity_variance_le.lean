-- Prove2me | Theorems.Thm_CohnElkies_upper_shortShellDensity_variance_le
-- name    : CohnElkies.upper_shortShellDensity_variance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/cab21caf-ae9d-4d75-a9a9-dea23fb3341e
-- title:
--   CohnElkies.upper_shortShellDensity_variance_le
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

theorem CohnElkies.upper_shortShellDensity_variance_le
    {ε δ a A : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A) :
    (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a) ≤
      (1 / 2 : ℝ) * Real.exp (δ * A) := by sorry
