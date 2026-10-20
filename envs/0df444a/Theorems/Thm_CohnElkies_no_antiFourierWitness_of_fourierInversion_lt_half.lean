-- Prove2me | Theorems.Thm_CohnElkies_no_antiFourierWitness_of_fourierInversion_lt_half
-- name    : CohnElkies.no_antiFourierWitness_of_fourierInversion_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/28431275-1349-4141-8af5-11afd81802a3
-- title:
--   CohnElkies.no_antiFourierWitness_of_fourierInversion_lt_half
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

theorem CohnElkies.no_antiFourierWitness_of_fourierInversion_lt_half
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (normalizedRadialLogProfile hd w.function R v : ℂ) =
        (Real.exp (a * v) : ℂ) *
          ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v))
    (hsmall : ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a <
      (1 / 2 : ℝ)) : False := by sorry
