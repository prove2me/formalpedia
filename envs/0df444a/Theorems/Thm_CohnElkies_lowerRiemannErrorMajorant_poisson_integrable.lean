-- Prove2me | Theorems.Thm_CohnElkies_lowerRiemannErrorMajorant_poisson_integrable
-- name    : CohnElkies.lowerRiemannErrorMajorant_poisson_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/fa1fc021-acec-4b70-9f7f-0d3520a4eaeb
-- title:
--   CohnElkies.lowerRiemannErrorMajorant_poisson_integrable
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

theorem CohnElkies.lowerRiemannErrorMajorant_poisson_integrable
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T *
        lowerRiemannErrorMajorant T) := by sorry
