-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_antitoneOn
-- name    : CohnElkies.lowerGammaBoundaryLog_integer_antitoneOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/1f6d5d2a-d5ab-498e-8636-38b210e51e6a
-- title:
--   CohnElkies.lowerGammaBoundaryLog_integer_antitoneOn
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
open scoped FourierTransform Interval RealInnerProductSpace Topology

theorem CohnElkies.lowerGammaBoundaryLog_integer_antitoneOn
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog (k : ℝ) R)
      (Ioi (0 : ℝ)) := by sorry
