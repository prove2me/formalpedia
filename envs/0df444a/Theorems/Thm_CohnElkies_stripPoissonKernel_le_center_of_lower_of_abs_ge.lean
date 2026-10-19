-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonKernel_le_center_of_lower_of_abs_ge
-- name    : CohnElkies.stripPoissonKernel_le_center_of_lower_of_abs_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/09ba16b5-6636-4463-bcd8-c2c9aa1ab0d5
-- title:
--   CohnElkies.stripPoissonKernel_le_center_of_lower_of_abs_ge
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

theorem CohnElkies.stripPoissonKernel_le_center_of_lower_of_abs_ge
    {σ δ T : ℝ}
    (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    (hδ : 0 < δ) (hT : δ ≤ |T|) :
    stripPoissonKernel σ T ≤
      (1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)) *
        stripPoissonKernel 0 T := by sorry
