-- Prove2me | Theorems.Thm_CohnElkies_eventually_lowerPoissonEndpointSharpCoefficient_neg
-- name    : CohnElkies.eventually_lowerPoissonEndpointSharpCoefficient_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/97695ef9-c2e5-4118-a899-1b1e8d449aa2
-- title:
--   CohnElkies.eventually_lowerPoissonEndpointSharpCoefficient_neg
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
open scoped Interval Topology

theorem CohnElkies.eventually_lowerPoissonEndpointSharpCoefficient_neg
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    ∀ᶠ σ : ℝ in 𝓝[<] 1,
      Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        lowerPoissonEndpointExpectation σ < 0 := by sorry
