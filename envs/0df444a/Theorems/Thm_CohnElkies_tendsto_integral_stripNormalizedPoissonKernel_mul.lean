-- Prove2me | Theorems.Thm_CohnElkies_tendsto_integral_stripNormalizedPoissonKernel_mul
-- name    : CohnElkies.tendsto_integral_stripNormalizedPoissonKernel_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/0a936645-ea9e-4434-8d8c-5ca09cc4a7d3
-- title:
--   CohnElkies.tendsto_integral_stripNormalizedPoissonKernel_mul
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

theorem CohnElkies.tendsto_integral_stripNormalizedPoissonKernel_mul
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hmajor : Integrable
      (fun T : ℝ => stripPoissonExponentialMajorant T * ‖f T‖)) :
    Tendsto
      (fun σ : ℝ =>
        ∫ T : ℝ, stripNormalizedPoissonKernel σ T * f T)
      (𝓝[<] 1)
      (𝓝 (∫ T : ℝ, limitingStripPoissonDensity T * f T)) := by sorry
