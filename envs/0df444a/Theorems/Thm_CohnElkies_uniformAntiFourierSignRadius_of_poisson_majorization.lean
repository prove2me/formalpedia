-- Prove2me | Theorems.Thm_CohnElkies_uniformAntiFourierSignRadius_of_poisson_majorization
-- name    : CohnElkies.uniformAntiFourierSignRadius_of_poisson_majorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/81664c05-f90e-497d-9d35-a65d1ba68051
-- title:
--   CohnElkies.uniformAntiFourierSignRadius_of_poisson_majorization
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

theorem CohnElkies.uniformAntiFourierSignRadius_of_poisson_majorization
    (hpoisson :
      ∀ {d : ℕ} (hd : 0 < d) {R : ℝ} (_hR : 0 < R)
        (w : AntiFourierWitness d R)
        {σ : ℝ} (_hσbelow : -1 < σ) (_hσabove : σ < 1)
        (s : ℝ),
        ‖normalizedRadialMellinStrip hd w.function R
          ((s : ℂ) + Complex.I *
            (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s)) :
    UniformAntiFourierSignRadius := by sorry
