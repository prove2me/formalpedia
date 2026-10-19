-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_continuousOn
-- name    : CohnElkies.lowerGammaBoundaryLog_continuousOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/88a0bb2a-ee5b-4941-b038-fae4dbfd2795
-- title:
--   CohnElkies.lowerGammaBoundaryLog_continuousOn
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

theorem CohnElkies.lowerGammaBoundaryLog_continuousOn
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) {S : Set ℝ}
    (hS : ∀ y ∈ S, y ≠ 0) :
    ContinuousOn (lowerGammaBoundaryLog ℓ R) S := by sorry
