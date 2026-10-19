-- Prove2me | Theorems.Thm_CohnElkies_upperGammaShifted_modulus_eq_exp_neg_damping
-- name    : CohnElkies.upperGammaShifted_modulus_eq_exp_neg_damping
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/bc3583a2-d8fc-497a-8b7f-f902946fae20
-- title:
--   CohnElkies.upperGammaShifted_modulus_eq_exp_neg_damping
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
open scoped Topology BigOperators

theorem CohnElkies.upperGammaShifted_modulus_eq_exp_neg_damping
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    ‖Complex.Gamma
        (((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ =
      Real.Gamma (ℓ * η / 2) *
        Real.exp (-upperGammaDamping ℓ η T) := by sorry
