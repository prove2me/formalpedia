-- Prove2me | Theorems.Thm_CohnElkies_integral_radialProfile_re
-- name    : CohnElkies.integral_radialProfile_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/519c32a6-8d6a-453f-b2b8-cc017c1e05cc
-- title:
--   CohnElkies.integral_radialProfile_re
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

theorem CohnElkies.integral_radialProfile_re {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g) :
    (∫ x : Euclidean d, (g x).re) =
      radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * (radialProfile hd g r).re := by sorry
