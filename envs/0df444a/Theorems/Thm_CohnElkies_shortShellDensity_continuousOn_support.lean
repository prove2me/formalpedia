-- Prove2me | Theorems.Thm_CohnElkies_shortShellDensity_continuousOn_support
-- name    : CohnElkies.shortShellDensity_continuousOn_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/6d08357d-a1ae-423f-9952-0309011c379b
-- title:
--   CohnElkies.shortShellDensity_continuousOn_support
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

theorem CohnElkies.shortShellDensity_continuousOn_support
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (shortShellDensity ε)
      (Icc (shortCutoff ε) (shortEndpoint ε)) := by sorry
