-- Prove2me | Theorems.Thm_CohnElkies_saddleMellinInversePower_shiftedLine_integral_norm
-- name    : CohnElkies.saddleMellinInversePower_shiftedLine_integral_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/8dc8a110-c0a0-4653-831f-c74ea732444d
-- title:
--   CohnElkies.saddleMellinInversePower_shiftedLine_integral_norm
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
open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology

theorem CohnElkies.saddleMellinInversePower_shiftedLine_integral_norm
    {r a : ℝ} (hr : 0 < r)
    (F : ℂ → ℂ)
    (hF : Integrable
      (fun t : ℝ => F ((a : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ t : ℝ,
      ‖saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        F ((a : ℂ) + (t : ℂ) * Complex.I)‖) =
      r ^ (-a) *
        (∫ t : ℝ,
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by sorry
