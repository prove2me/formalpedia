-- Prove2me | Theorems.Thm_CohnElkies_stripRegularizedOuter_integrable_of_exp_integrable
-- name    : CohnElkies.stripRegularizedOuter_integrable_of_exp_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/e744d047-a167-4621-905d-ee28179ed6d3
-- title:
--   CohnElkies.stripRegularizedOuter_integrable_of_exp_integrable
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
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

theorem CohnElkies.stripRegularizedOuter_integrable_of_exp_integrable
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) * b y)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ z y *
          (b y : ℂ)) := by sorry
