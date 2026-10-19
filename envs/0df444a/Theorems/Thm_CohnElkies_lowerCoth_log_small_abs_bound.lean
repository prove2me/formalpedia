-- Prove2me | Theorems.Thm_CohnElkies_lowerCoth_log_small_abs_bound
-- name    : CohnElkies.lowerCoth_log_small_abs_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/9e5a4e84-9bf4-439c-b323-60eb49bd728f
-- title:
--   CohnElkies.lowerCoth_log_small_abs_bound
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

theorem CohnElkies.lowerCoth_log_small_abs_bound
    {y : ℝ} (hy : y ≠ 0) (hsmall : |y| ≤ 1) :
    Real.log (lowerCoth (Real.pi * |y| / 2)) ≤
      Real.pi + |Real.log Real.pi| +
        3 * (|Real.log (|y|)| + |Real.log (2 : ℝ)|) := by sorry
