-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_support
-- name    : CohnElkies.lowerGammaScaledPositivePart_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/fd4902fb-a7fb-48e8-ae2c-75118db15fe3
-- title:
--   CohnElkies.lowerGammaScaledPositivePart_support
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

theorem CohnElkies.lowerGammaScaledPositivePart_support
    {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Function.support (lowerGammaScaledPositivePart d c) ⊆
      Icc (-(max 1 (8 * Real.pi * c ^ 2)))
        (max 1 (8 * Real.pi * c ^ 2)) := by sorry
