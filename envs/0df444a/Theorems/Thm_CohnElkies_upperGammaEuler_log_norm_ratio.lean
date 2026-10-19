-- Prove2me | Theorems.Thm_CohnElkies_upperGammaEuler_log_norm_ratio
-- name    : CohnElkies.upperGammaEuler_log_norm_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/d9c83593-798e-47fe-b207-01fee8102b84
-- title:
--   CohnElkies.upperGammaEuler_log_norm_ratio
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
open scoped Topology BigOperators

theorem CohnElkies.upperGammaEuler_log_norm_ratio
    {m : ℝ} (hm : 0 < m) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    Real.log
      (‖Complex.GammaSeq
          ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
        ‖Complex.GammaSeq (m : ℂ) n‖) =
      -(∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖(m : ℂ) + Complex.I * (b : ℂ) + (k : ℂ)‖ /
            (m + (k : ℝ)))) := by sorry
