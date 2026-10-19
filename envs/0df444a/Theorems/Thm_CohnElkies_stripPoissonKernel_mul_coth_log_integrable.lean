-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonKernel_mul_coth_log_integrable
-- name    : CohnElkies.stripPoissonKernel_mul_coth_log_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/8bb80a5a-edce-4ff0-bb1b-337fe85ed6f2
-- title:
--   CohnElkies.stripPoissonKernel_mul_coth_log_integrable
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

theorem CohnElkies.stripPoissonKernel_mul_coth_log_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T *
        Real.log (lowerCoth (Real.pi * |T| / 2))) := by sorry
