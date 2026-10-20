-- Prove2me | Theorems.Thm_CohnElkies_upperNegativeContour_reflectedGamma_damping_exp_le_cosh
-- name    : CohnElkies.upperNegativeContour_reflectedGamma_damping_exp_le_cosh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/0b2496a6-c6e7-484a-ae24-160ed7b7f59b
-- title:
--   CohnElkies.upperNegativeContour_reflectedGamma_damping_exp_le_cosh
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

theorem CohnElkies.upperNegativeContour_reflectedGamma_damping_exp_le_cosh
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    Real.exp
        (2 * upperGammaDamping ℓ
          (saddleNegativeGammaRate ℓ N) (-s / ℓ)) ≤
      Real.cosh (Real.pi * (s / 2)) := by sorry
