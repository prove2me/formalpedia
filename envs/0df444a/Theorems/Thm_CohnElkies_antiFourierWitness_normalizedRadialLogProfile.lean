-- Prove2me | Theorems.Thm_CohnElkies_antiFourierWitness_normalizedRadialLogProfile
-- name    : CohnElkies.antiFourierWitness_normalizedRadialLogProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/767f86bd-e87d-4653-b2de-e821331af8fd
-- title:
--   CohnElkies.antiFourierWitness_normalizedRadialLogProfile
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
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem CohnElkies.antiFourierWitness_normalizedRadialLogProfile
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    let φ := normalizedRadialLogProfile hd w.function R
    Integrable φ ∧
      (∫ v : ℝ, φ v) = 0 ∧
      (∫ v : ℝ, |φ v|) = 1 ∧
      (∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) := by sorry
