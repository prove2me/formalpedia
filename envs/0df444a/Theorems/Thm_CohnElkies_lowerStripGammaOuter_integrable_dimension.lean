-- Prove2me | Theorems.Thm_CohnElkies_lowerStripGammaOuter_integrable_dimension
-- name    : CohnElkies.lowerStripGammaOuter_integrable_dimension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/ff29fe13-9742-4fc1-b28e-5e296fa51345
-- title:
--   CohnElkies.lowerStripGammaOuter_integrable_dimension
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

theorem CohnElkies.lowerStripGammaOuter_integrable_dimension
    {d : ℕ} (hd : 0 < d) {R : ℝ} {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹'
      Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2) z y *
          (lowerGammaBoundaryLog ((d : ℝ) / 2) R y : ℂ)) := by sorry
