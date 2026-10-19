-- Prove2me | Theorems.Thm_CohnElkies_norm_complexLaplaceKernel
-- name    : CohnElkies.norm_complexLaplaceKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/f797dff2-8b57-46bd-a39d-d718d2eca259
-- title:
--   CohnElkies.norm_complexLaplaceKernel
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

theorem CohnElkies.norm_complexLaplaceKernel (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-z * (x : ℂ))‖ =
      Real.exp (-z.re * x) := by sorry
