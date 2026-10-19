-- Prove2me | Theorems.Thm_CohnElkies_saddle_shellInterval_hyperbolic_sub_oscillatory
-- name    : CohnElkies.saddle_shellInterval_hyperbolic_sub_oscillatory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/780a586a-b7c0-46f0-b44d-9f3e798e84e0
-- title:
--   CohnElkies.saddle_shellInterval_hyperbolic_sub_oscillatory
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

theorem CohnElkies.saddle_shellInterval_hyperbolic_sub_oscillatory
    (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (T u : ℝ) :
    (∫ x in a..b,
        w x * (Real.cosh (x * u) - 1)) -
      (∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1)) =
      ∫ x in a..b,
        w x * Real.cosh (x * u) *
          (1 - Real.cos (x * T)) := by sorry
