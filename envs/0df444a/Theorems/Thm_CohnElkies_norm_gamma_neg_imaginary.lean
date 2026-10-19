-- Prove2me | Theorems.Thm_CohnElkies_norm_gamma_neg_imaginary
-- name    : CohnElkies.norm_gamma_neg_imaginary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/a4a8961c-d720-4d00-bfbf-257d7806485a
-- title:
--   CohnElkies.norm_gamma_neg_imaginary
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

theorem CohnElkies.norm_gamma_neg_imaginary (y : ℝ) :
    ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by sorry
