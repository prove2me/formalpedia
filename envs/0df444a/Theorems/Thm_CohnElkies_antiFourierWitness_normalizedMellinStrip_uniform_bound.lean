-- Prove2me | Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_uniform_bound
-- name    : CohnElkies.antiFourierWitness_normalizedMellinStrip_uniform_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/76265480-1fba-4b21-a61a-7a515673cbdb
-- title:
--   CohnElkies.antiFourierWitness_normalizedMellinStrip_uniform_bound
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

theorem CohnElkies.antiFourierWitness_normalizedMellinStrip_uniform_bound
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ,
        -((d : ℝ) / 2) ≤ z.im →
        z.im ≤ (d : ℝ) / 2 →
          ‖normalizedRadialMellinStrip hd w.function R z‖ ≤ C := by sorry
