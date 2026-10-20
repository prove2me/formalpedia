-- Prove2me | Theorems.Thm_CohnElkies_cos_le_quartic
-- name    : CohnElkies.cos_le_quartic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/19bef024-971f-45eb-900a-ddc4f5c27428
-- title:
--   CohnElkies.cos_le_quartic
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

theorem CohnElkies.cos_le_quartic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96 : ℝ) := by sorry
