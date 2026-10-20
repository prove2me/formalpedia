-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaScaledCappedLowerClip_poisson_tendsto
-- name    : CohnElkies.lowerGammaScaledCappedLowerClip_poisson_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/db00bbd7-9b4b-4add-9425-c5a2e70757f6
-- title:
--   CohnElkies.lowerGammaScaledCappedLowerClip_poisson_tendsto
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
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.lowerGammaScaledCappedLowerClip_poisson_tendsto
    {d : ℕ} (hd : 0 < d) {c D σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip
            d c D (n : ℝ) Y)
      atTop
      (𝓝 (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))) := by sorry
