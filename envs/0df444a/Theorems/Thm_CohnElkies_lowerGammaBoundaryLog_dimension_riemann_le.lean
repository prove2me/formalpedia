-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_riemann_le
-- name    : CohnElkies.lowerGammaBoundaryLog_dimension_riemann_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/3105db7c-c719-40f2-8199-416142fda91c
-- title:
--   CohnElkies.lowerGammaBoundaryLog_dimension_riemann_le
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

theorem CohnElkies.lowerGammaBoundaryLog_dimension_riemann_le
    {d : ℕ} (hd : 2 ≤ d) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R
        (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (Real.pi * R ^ 2 / ((d : ℝ) / 2)) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by sorry
