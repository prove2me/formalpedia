-- Prove2me | Theorems.Thm_CohnElkies_complexFrullaniParameter_integrable
-- name    : CohnElkies.complexFrullaniParameter_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/f4b5c9cd-b32e-43a1-8319-d041a819f1d3
-- title:
--   CohnElkies.complexFrullaniParameter_integrable
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
open scoped Topology

theorem CohnElkies.complexFrullaniParameter_integrable
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Integrable
      (Function.uncurry (fun s x : ℝ =>
        (w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Ioi 0))) := by sorry
