-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
-- name    : CohnElkies.lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/ea21ece8-f367-4a17-8404-62388d6c257a
-- title:
--   CohnElkies.lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
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

theorem CohnElkies.lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
    {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (R D : ℝ)
    (hgamma : Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) * lowerGammaBoundaryLog ℓ R y)) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryCapped ℓ R D y) := by sorry
