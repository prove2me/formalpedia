-- Prove2me | Theorems.Thm_CohnElkies_normalizedRadialLogProfile_eq
-- name    : CohnElkies.normalizedRadialLogProfile_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/31a4c205-35b3-49eb-9845-133b6d909661
-- title:
--   CohnElkies.normalizedRadialLogProfile_eq
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
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem CohnElkies.normalizedRadialLogProfile_eq {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) :
    normalizedRadialLogProfile hd g R v =
      (radialSurfaceArea d / radialL1Mass g) *
        ((R * Real.exp v) *
          ((R * Real.exp v) ^ (d - 1) *
            (radialProfile hd g (R * Real.exp v)).re)) := by sorry
