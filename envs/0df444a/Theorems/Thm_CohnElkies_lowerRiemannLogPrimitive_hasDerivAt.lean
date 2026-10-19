-- Prove2me | Theorems.Thm_CohnElkies_lowerRiemannLogPrimitive_hasDerivAt
-- name    : CohnElkies.lowerRiemannLogPrimitive_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/a2b92b90-c37b-4668-9b34-8bcf7f3997fb
-- title:
--   CohnElkies.lowerRiemannLogPrimitive_hasDerivAt
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

theorem CohnElkies.lowerRiemannLogPrimitive_hasDerivAt
    {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (lowerRiemannLogPrimitive T)
      (lowerRiemannLog T x) x := by sorry
