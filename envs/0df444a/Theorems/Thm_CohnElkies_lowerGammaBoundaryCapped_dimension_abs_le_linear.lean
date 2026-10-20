-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_abs_le_linear
-- name    : CohnElkies.lowerGammaBoundaryCapped_dimension_abs_le_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/d8e549de-7e03-4bac-b07e-de4e2f1c3a45
-- title:
--   CohnElkies.lowerGammaBoundaryCapped_dimension_abs_le_linear
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
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem CohnElkies.lowerGammaBoundaryCapped_dimension_abs_le_linear
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ,
        |lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y| ≤
            A * (1 + |y|) := by sorry
