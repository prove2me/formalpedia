-- Prove2me | Theorems.Thm_CohnElkies_lowerStripCappedPoisson_tendsto_radius
-- name    : CohnElkies.lowerStripCappedPoisson_tendsto_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/276271ab-efc1-4191-a50d-ecbfd79e252a
-- title:
--   CohnElkies.lowerStripCappedPoisson_tendsto_radius
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

theorem CohnElkies.lowerStripCappedPoisson_tendsto_radius
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ T : ℝ,
          stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2)
              R (n : ℝ)
              (s - ((d : ℝ) / 2) * T))
      atTop
      (𝓝 (lowerStripPoissonMajorant ((d : ℝ) / 2)
        R σ s)) := by sorry
