-- Prove2me | Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_shifted_integrable
-- name    : CohnElkies.antiFourierWitness_normalizedMellinStrip_shifted_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/8219aaef-9c51-4cc6-b44e-a5206245a9de
-- title:
--   CohnElkies.antiFourierWitness_normalizedMellinStrip_shifted_integrable
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

theorem CohnElkies.antiFourierWitness_normalizedMellinStrip_shifted_integrable
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ =>
      normalizedRadialMellinStrip hd w.function R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) := by sorry
