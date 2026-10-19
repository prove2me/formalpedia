-- Prove2me | Theorems.Thm_CohnElkies_norm_gamma_half_add_imaginary_sq
-- name    : CohnElkies.norm_gamma_half_add_imaginary_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/73c5af56-409c-47db-8fd7-e1dceffad38c
-- title:
--   CohnElkies.norm_gamma_half_add_imaginary_sq
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

theorem CohnElkies.norm_gamma_half_add_imaginary_sq (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * x) := by sorry
