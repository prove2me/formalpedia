-- Prove2me | Theorems.Thm_CohnElkies_norm_schwartz_imaginaryRiesz_integral_le_L1
-- name    : CohnElkies.norm_schwartz_imaginaryRiesz_integral_le_L1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/5926fa0e-7fc9-4ea8-bc97-39f77cccf15e
-- title:
--   CohnElkies.norm_schwartz_imaginaryRiesz_integral_le_L1
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

theorem CohnElkies.norm_schwartz_imaginaryRiesz_integral_le_L1 {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    ‖∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      radialL1Mass f := by sorry
