-- Prove2me | Theorems.Thm_CohnElkies_no_antiFourierWitness_of_interiorMellinL1_lt_half
-- name    : CohnElkies.no_antiFourierWitness_of_interiorMellinL1_lt_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/55bb56ef-374b-4382-ba52-cd74380423a5
-- title:
--   CohnElkies.no_antiFourierWitness_of_interiorMellinL1_lt_half
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

theorem CohnElkies.no_antiFourierWitness_of_interiorMellinL1_lt_half
    {d : ℕ} (hd : 0 < d) {R σ : ℝ} (hR : 0 < R)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hsmall :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hd w.function R
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) <
        (1 / 2 : ℝ)) : False := by sorry
