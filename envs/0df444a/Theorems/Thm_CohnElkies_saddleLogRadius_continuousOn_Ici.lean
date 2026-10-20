-- Prove2me | Theorems.Thm_CohnElkies_saddleLogRadius_continuousOn_Ici
-- name    : CohnElkies.saddleLogRadius_continuousOn_Ici
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/c08971d0-af72-49d7-9842-62155e075d6a
-- title:
--   CohnElkies.saddleLogRadius_continuousOn_Ici
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

theorem CohnElkies.saddleLogRadius_continuousOn_Ici
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {d : ℕ} (hd : 0 < d)
    {u₀ : ℝ} (hu₀ : -1 < u₀) :
    ContinuousOn (saddleLogRadius ε d) (Ici u₀) := by sorry
