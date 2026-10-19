-- Prove2me | Theorems.Thm_CohnElkies_lowerWallisRegularizedPhaseKernel_eq_add
-- name    : CohnElkies.lowerWallisRegularizedPhaseKernel_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/6f69069f-0527-4867-b073-7c9402069254
-- title:
--   CohnElkies.lowerWallisRegularizedPhaseKernel_eq_add
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

theorem CohnElkies.lowerWallisRegularizedPhaseKernel_eq_add
    (a u t : ℝ) :
    lowerWallisRegularizedPhaseKernel a u t =
      lowerWallisPhaseKernel u t +
        ((1 - Real.exp (-t)) *
          (Real.exp (-a * t) - 1) * Real.cos (u * t)) /
            t ^ 2 := by sorry
