-- Prove2me | Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_bottom_norm_eq
-- name    : CohnElkies.normalizedRadialMellinStrip_bottom_norm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/3ab6b335-836a-44bd-b5c1-307d36e33407
-- title:
--   CohnElkies.normalizedRadialMellinStrip_bottom_norm_eq
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
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

theorem CohnElkies.normalizedRadialMellinStrip_bottom_norm_eq {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ =
      (radialSurfaceArea d / radialL1Mass f) *
        Real.exp ((d : ℝ) * Real.log R) *
        ‖mellin (radialProfile hd f)
          (-(Complex.I * (y : ℂ)))‖ := by sorry
