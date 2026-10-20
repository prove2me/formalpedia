-- Prove2me | Theorems.Thm_CohnElkies_saddleGaussian_cubic_tail_integral_le
-- name    : CohnElkies.saddleGaussian_cubic_tail_integral_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/5b42da6e-ce84-47d4-90e0-d5406facb4d9
-- title:
--   CohnElkies.saddleGaussian_cubic_tail_integral_le
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
open Filter Set MeasureTheory
open scoped Topology

theorem CohnElkies.saddleGaussian_cubic_tail_integral_le
    {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      2 * Real.exp (-(k / 4) * R ^ 2) *
        Real.sqrt (Real.pi / (k / 4)) := by sorry
