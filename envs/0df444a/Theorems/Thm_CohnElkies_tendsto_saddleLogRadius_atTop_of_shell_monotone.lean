-- Prove2me | Theorems.Thm_CohnElkies_tendsto_saddleLogRadius_atTop_of_shell_monotone
-- name    : CohnElkies.tendsto_saddleLogRadius_atTop_of_shell_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/ced09a38-6df7-45ee-b010-eef41c0620f1
-- title:
--   CohnElkies.tendsto_saddleLogRadius_atTop_of_shell_monotone
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

theorem CohnElkies.tendsto_saddleLogRadius_atTop_of_shell_monotone
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {d : ℕ} (hd : 0 < d)
    (hmono : MonotoneOn (saddleSourceShellDerivative ε)
      (Ici (1 + ε / 2))) :
    Tendsto (saddleLogRadius ε d) atTop atTop := by sorry
