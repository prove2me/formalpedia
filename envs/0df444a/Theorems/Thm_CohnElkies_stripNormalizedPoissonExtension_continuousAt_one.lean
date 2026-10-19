-- Prove2me | Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_continuousAt_one
-- name    : CohnElkies.stripNormalizedPoissonExtension_continuousAt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/a49b54ad-6b0f-48f0-a7be-698cbf9bd2ff
-- title:
--   CohnElkies.stripNormalizedPoissonExtension_continuousAt_one
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
open scoped Interval Topology

theorem CohnElkies.stripNormalizedPoissonExtension_continuousAt_one (T : ℝ) :
    ContinuousAt (fun σ : ℝ => stripNormalizedPoissonExtension σ T)
      1 := by sorry
