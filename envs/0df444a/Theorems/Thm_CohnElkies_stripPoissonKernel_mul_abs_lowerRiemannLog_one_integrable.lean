-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
-- name    : CohnElkies.stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/c75e02ac-01aa-49a5-bd94-f5ac8f6c5da2
-- title:
--   CohnElkies.stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
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

theorem CohnElkies.stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * |lowerRiemannLog T 1|) := by sorry
