-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_integral
-- name    : CohnElkies.stripPoissonWeightedMeasure_integral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/0470c716-d07c-4e10-aa7e-0acb7691bf6f
-- title:
--   CohnElkies.stripPoissonWeightedMeasure_integral
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

theorem CohnElkies.stripPoissonWeightedMeasure_integral
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (f : ℝ → ℝ) (s : ℝ) :
    (∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ s) =
      ∫ x : ℝ, stripPoissonKernel σ (s - x) * f x := by sorry
