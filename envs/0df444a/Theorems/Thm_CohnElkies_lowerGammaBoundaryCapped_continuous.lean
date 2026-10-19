-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous
-- name    : CohnElkies.lowerGammaBoundaryCapped_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/776c118b-0e1e-4be9-8311-25438c2f8ae5
-- title:
--   CohnElkies.lowerGammaBoundaryCapped_continuous
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

theorem CohnElkies.lowerGammaBoundaryCapped_continuous
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R D : ℝ) :
    Continuous (lowerGammaBoundaryCapped ℓ R D) := by sorry
