-- Prove2me | Theorems.Thm_CohnElkies_complexShellInterval_continuous
-- name    : CohnElkies.complexShellInterval_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/cd9c2783-5d26-41ac-bb9d-e8f3252d3751
-- title:
--   CohnElkies.complexShellInterval_continuous
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

theorem CohnElkies.complexShellInterval_continuous
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun z : ℂ =>
      ∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) := by sorry
