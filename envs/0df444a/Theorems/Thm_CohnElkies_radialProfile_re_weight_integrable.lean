-- Prove2me | Theorems.Thm_CohnElkies_radialProfile_re_weight_integrable
-- name    : CohnElkies.radialProfile_re_weight_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/0d1e3a59-b6ec-4023-b7f7-fda7c5df857f
-- title:
--   CohnElkies.radialProfile_re_weight_integrable
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
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem CohnElkies.radialProfile_re_weight_integrable {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g) :
    IntegrableOn
      (fun r : ℝ => r ^ (d - 1) * (radialProfile hd g r).re)
      (Ioi 0) := by sorry
