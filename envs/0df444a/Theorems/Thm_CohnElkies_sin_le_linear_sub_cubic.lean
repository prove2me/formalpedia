-- Prove2me | Theorems.Thm_CohnElkies_sin_le_linear_sub_cubic
-- name    : CohnElkies.sin_le_linear_sub_cubic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/1aebdc62-1a5b-49b8-a238-80896f49c661
-- title:
--   CohnElkies.sin_le_linear_sub_cubic
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
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

theorem CohnElkies.sin_le_linear_sub_cubic {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ (1 / 2 : ℝ)) :
    Real.sin x ≤ x - (4 / 25 : ℝ) * x ^ 3 := by sorry
