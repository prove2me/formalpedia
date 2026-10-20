-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceTailIntegrand_continuous
-- name    : CohnElkies.saddleSourceTailIntegrand_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/0ceb05a0-74a9-4b67-8f10-08dce373b58e
-- title:
--   CohnElkies.saddleSourceTailIntegrand_continuous
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
open Filter Set MeasureTheory
open scoped Topology

theorem CohnElkies.saddleSourceTailIntegrand_continuous
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by sorry
