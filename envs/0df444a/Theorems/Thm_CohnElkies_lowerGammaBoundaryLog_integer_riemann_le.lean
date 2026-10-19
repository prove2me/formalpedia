-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_riemann_le
-- name    : CohnElkies.lowerGammaBoundaryLog_integer_riemann_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/c1776084-d22b-4569-853e-2348970c9b3a
-- title:
--   CohnElkies.lowerGammaBoundaryLog_integer_riemann_le
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
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.lowerGammaBoundaryLog_integer_riemann_le
    {k : ℕ} (hk : 0 < k) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R ((k : ℝ) * T) ≤
      (k : ℝ) *
        (Real.log (Real.pi * R ^ 2 / (k : ℝ)) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by sorry
