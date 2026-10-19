-- Prove2me | Theorems.Thm_CohnElkies_complexFrullaniShiftKernel_norm_le_exp
-- name    : CohnElkies.complexFrullaniShiftKernel_norm_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/3be362e8-be41-430e-910d-5b0451ba72ff
-- title:
--   CohnElkies.complexFrullaniShiftKernel_norm_le_exp
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

theorem CohnElkies.complexFrullaniShiftKernel_norm_le_exp
    (z : ℂ) {s x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
      (‖(1 : ℂ) - z‖ + 1) *
        Real.exp (-(min z.re 1) * x) := by sorry
