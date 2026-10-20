-- Prove2me | Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_bottom_norm_le_gamma
-- name    : CohnElkies.normalizedRadialMellinStrip_bottom_norm_le_gamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/b8c893c4-92e9-448f-9cc8-f751b021f918
-- title:
--   CohnElkies.normalizedRadialMellinStrip_bottom_norm_le_gamma
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

theorem CohnElkies.normalizedRadialMellinStrip_bottom_norm_le_gamma {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hanti : (𝓕 f : TestFunction d) = -f)
    (hnonzero : f ≠ 0)
    (R : ℝ) (hR : 0 < R) (y : ℝ) (hy : y ≠ 0) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log
            ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖) := by sorry
