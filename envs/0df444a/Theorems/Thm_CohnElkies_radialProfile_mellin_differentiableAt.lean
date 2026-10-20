-- Prove2me | Theorems.Thm_CohnElkies_radialProfile_mellin_differentiableAt
-- name    : CohnElkies.radialProfile_mellin_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/bc0f5151-df45-4c6b-80c8-8da68b83e3fa
-- title:
--   CohnElkies.radialProfile_mellin_differentiableAt
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

theorem CohnElkies.radialProfile_mellin_differentiableAt {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (s : ℂ) (hs : -2 < s.re) :
    DifferentiableAt ℂ (mellin (radialProfile hd f)) s := by sorry
