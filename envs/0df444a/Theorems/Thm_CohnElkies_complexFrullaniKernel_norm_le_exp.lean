-- Prove2me | Theorems.Thm_CohnElkies_complexFrullaniKernel_norm_le_exp
-- name    : CohnElkies.complexFrullaniKernel_norm_le_exp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/399187a2-ef36-4f85-a46b-28d9561ef1bf
-- title:
--   CohnElkies.complexFrullaniKernel_norm_le_exp
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
open scoped Topology

theorem CohnElkies.complexFrullaniKernel_norm_le_exp
    (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖complexFrullaniKernel z w x‖ ≤
      ‖w - z‖ *
        Real.exp (-(min z.re w.re) * x) := by sorry
