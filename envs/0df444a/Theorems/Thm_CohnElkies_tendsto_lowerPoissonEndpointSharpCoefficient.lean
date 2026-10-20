-- Prove2me | Theorems.Thm_CohnElkies_tendsto_lowerPoissonEndpointSharpCoefficient
-- name    : CohnElkies.tendsto_lowerPoissonEndpointSharpCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/fc8a03ea-7d31-4dc7-9300-944a690734d9
-- title:
--   CohnElkies.tendsto_lowerPoissonEndpointSharpCoefficient
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

theorem CohnElkies.tendsto_lowerPoissonEndpointSharpCoefficient
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun σ : ℝ =>
        Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ)
      (𝓝[<] 1)
      (𝓝 (Real.log (Real.pi ^ 2 * c ^ 2))) := by sorry
