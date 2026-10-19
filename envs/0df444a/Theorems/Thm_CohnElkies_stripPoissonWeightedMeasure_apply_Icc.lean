-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_apply_Icc
-- name    : CohnElkies.stripPoissonWeightedMeasure_apply_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/713f54f1-a046-4d62-943d-69d548eea8b1
-- title:
--   CohnElkies.stripPoissonWeightedMeasure_apply_Icc
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

theorem CohnElkies.stripPoissonWeightedMeasure_apply_Icc
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (s a b : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc a b) =
      ENNReal.ofReal
        (∫ x in Icc a b,
          stripPoissonKernel σ (s - x)) := by sorry
