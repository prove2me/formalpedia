-- Prove2me | Theorems.Thm_CohnElkies_norm_radialProfile_eq_abs_re
-- name    : CohnElkies.norm_radialProfile_eq_abs_re
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/8ce8592e-2154-4938-88ee-bf9768f3fb47
-- title:
--   CohnElkies.norm_radialProfile_eq_abs_re
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

theorem CohnElkies.norm_radialProfile_eq_abs_re {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRealValued g) (r : ℝ) :
    ‖radialProfile hd g r‖ =
      |(radialProfile hd g r).re| := by sorry
