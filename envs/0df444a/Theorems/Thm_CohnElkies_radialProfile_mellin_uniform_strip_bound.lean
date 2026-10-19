-- Prove2me | Theorems.Thm_CohnElkies_radialProfile_mellin_uniform_strip_bound
-- name    : CohnElkies.radialProfile_mellin_uniform_strip_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/05db8e26-2e25-4403-8294-ec20d1533a32
-- title:
--   CohnElkies.radialProfile_mellin_uniform_strip_bound
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

theorem CohnElkies.radialProfile_mellin_uniform_strip_bound {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ (d : ℝ) →
        ‖mellin (radialProfile hd f) s‖ ≤ C := by sorry
