-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonPrimitive_centered_antitoneOn
-- name    : CohnElkies.stripPoissonPrimitive_centered_antitoneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/d2cb9639-8d48-488c-a900-110cd3640928
-- title:
--   CohnElkies.stripPoissonPrimitive_centered_antitoneOn
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

theorem CohnElkies.stripPoissonPrimitive_centered_antitoneOn
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn
      (fun s : ℝ =>
        stripPoissonPrimitive σ (s + r) -
          stripPoissonPrimitive σ (s - r))
      (Ici (0 : ℝ)) := by sorry
